-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .obviously




-- **** Begin caching stuff ****

-- **** Enable tactic block caching (just include) ****
import tactic.tcache.enable

-- Trace which declarations have blocks being cached
set_option trace.tcache true

-- Uncomment to clear the cache (recomment afterword)
-- #clear tcache

-- **** End of caching stuff ****




open category_theory

namespace category_theory.adjunctions

section

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{v₁ u₁} C] {D : Type u₂} [𝒟 : category.{v₂ u₂} D]
include 𝒞 𝒟

structure Adjunction (L : C ⥤ D) (R : D ⥤ C) :=
  (unit       : functor.id _ ⟹ (L ⋙ R))
  (counit     : (R ⋙ L) ⟹ functor.id _)
  (triangle_1 : ∀ X : D, (unit.app (R.obj X)) ≫ (R.map (counit.app X)) = 𝟙 (R.obj X))
  (triangle_2 : ∀ X : C, (L.map (unit.app X)) ≫ (counit.app (L.obj X)) = 𝟙 (L.obj X))

attribute [simp,search] Adjunction.triangle_1 Adjunction.triangle_2

lemma Adjunctions_pointwise_equal
  (L : C ⥤ D) (R : D ⥤ C) (A B : Adjunction L R)
  (w1 : A.unit = B.unit) (w2 : A.counit = B.counit) : A = B :=
  begin
    induction A,
    induction B,
    tidy
  end

@[simp,search] lemma Adjunction.unit_naturality {L : C ⥤ D} {R : D ⥤ C} (A : Adjunction L R) {X Y : C} (f : X ⟶ Y) : (A.unit.app X) ≫ (R.map (L.map f)) = f ≫ (A.unit.app Y) :=
by obviously

@[simp,search] lemma Adjunction.counit_naturality {L : C ⥤ D} {R : D ⥤ C} (A : Adjunction L R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (A.counit.app Y) = (A.counit.app X) ≫ f :=
by obviously

end

infix ` ⊣ `:50 := Adjunction

section
universes u₁ v₁

variables {C : Type u₁} [𝒞 : category.{v₁ u₁} C] {D : Type u₁} [𝒟 : category.{v₁ u₁} D]
include 𝒞 𝒟 

def hom_adjunction (L : C ⥤ D) (R : D ⥤ C) :=
    ((functor.prod L.op (functor.id D)) ⋙ (functor.hom D))
      ≅ 
    (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (functor.hom C)

def mate {L : C ⥤ D} {R : D ⥤ C} (A : hom_adjunction L R) {X : C} {Y : D} (f : (L.obj X) ⟶ Y) : 
  X ⟶ (R.obj Y) := 
((A.hom).app (op X, Y)) f

end
end category_theory.adjunctions

namespace category_theory.adjunctions

universes u v v₁ u₁ u₂ v₂ u₃ v₃ u₄ v₄

section
variables {A : Type u₁} [𝒜 : category.{v₁ u₁} A] {B : Type u₂} [ℬ : category.{v₂ u₂} B] {C : Type u₃} [𝒞 : category.{v₃ u₃} C] {D : Type u₄} [𝒟 : category.{v₄ u₄} D]
include 𝒜 ℬ 𝒞 𝒟

@[simp,search] lemma prod_obj' (F : A ⥤ B) (G : C ⥤ D) (a : A) (c : C) : (functor.prod F G).obj (a, c) = (F.obj a, G.obj c) := rfl
@[simp,search] lemma prod_app' {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟹ G) (β : H ⟹ I) (a : A) (c : C) : (nat_trans.prod α β).app (a, c) = (α.app a, β.app c) := rfl
end

variables {C : Type u₁} [𝒞 : category.{v₁ u₁} C] {D : Type u₁} [𝒟 : category.{v₁ u₁} D]
include 𝒞 𝒟
variables {L : C ⥤ D} {R : D ⥤ C}

@[reducible] private def Adjunction_to_HomAdjunction_morphism (A : L ⊣ R)
  : ((functor.prod L.op (functor.id D)) ⋙ (functor.hom D)) ⟹
                          (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (functor.hom C) :=
{ app := λ P,
    -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
    λ f, (A.unit.app (unop P.1)) ≫ (R.map f) }

@[reducible] private def Adjunction_to_HomAdjunction_inverse (A : L ⊣ R)
  : (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (functor.hom C) ⟹
                          ((functor.prod L.op (functor.id D)) ⋙ (functor.hom D)) :=
{ app := λ P,
    -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
    λ f, (L.map f) ≫ (A.counit.app P.2) }

def Adjunction_to_HomAdjunction (A : L ⊣ R) : hom_adjunction L R :=
{ hom := Adjunction_to_HomAdjunction_morphism A,
  inv := Adjunction_to_HomAdjunction_inverse A }

@[simp,search] lemma mate_of_L (A : hom_adjunction L R) {X Y : C} (f : X ⟶ Y) : (((A.hom).app (op X, L.obj X)) (𝟙 (L.obj X))) ≫
      (R.map (L.map f))
      = ((A.hom).app (op X, L.obj Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.hom (op X, L.obj X) (op X, L.obj Y) (𝟙 (op X), L.map f),
  have q := congr_fun p (L.map (𝟙 X)),
  tidy,
  erw category_theory.functor.map_id at q,
  obviously,
end

@[simp,search] lemma mate_of_L' (A : hom_adjunction L R) {X Y : C} (f : X ⟶ Y) : f ≫ (((A.hom).app (op Y, L.obj Y)) (𝟙 (L.obj Y)))
      = ((A.hom).app (op X, L.obj Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.hom (op Y, L.obj Y) (op X, L.obj Y) (f.op, 𝟙 (L.obj Y)),
  have q := congr_fun p (L.map (𝟙 Y)),
  obviously,
end

@[simp,search] lemma mate_of_R (A : hom_adjunction L R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (((A.inv).app (op (R.obj Y), Y)) (𝟙 (R.obj Y)))
      = ((A.inv).app (op (R.obj X), Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (op (R.obj Y), Y) (op (R.obj X), Y) ((R.map f).op, 𝟙 Y),
  have q := congr_fun p (R.map (𝟙 Y)),
  tidy,
end

@[simp,search] lemma mate_of_R' (A : hom_adjunction L R) {X Y : D} (f : X ⟶ Y) : (((A.inv).app (op (R.obj X), X)) (𝟙 (R.obj X))) ≫ f =
    ((A.inv).app (op (R.obj X), Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (op (R.obj X), X) (op (R.obj X), Y) (𝟙 (op (R.obj X)), f),
  have q := congr_fun p (R.map (𝟙 X)),
  obviously,
end

private def counit_from_HomAdjunction (A : hom_adjunction L R) : (R ⋙ L) ⟹ (functor.id _) :=
{ app := λ X : D, (A.inv.app (op (R.obj X), X)) (𝟙 (R.obj X)) }

private def unit_from_HomAdjunction (A : hom_adjunction L R) : (functor.id _) ⟹ (L ⋙ R) :=
{ app := λ X : C, (A.hom.app (op X, L.obj X)) (𝟙 (L.obj X)) }

end category_theory.adjunctions