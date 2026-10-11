/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.CategoryTheory.DG.Basic

/-!
# Differential graded categories as `A∞` categories

A differential graded category `C` over a commutative ring `R` is an `A∞` category on the same
objects whose higher operations vanish.  Its graded linear quiver
(`TauCeti.DGCategory.gradedLinearQuiver`) has as hom module from `X` to `Y` the direct sum
`⨁ n, Hom^n(X, Y)` of the morphisms of each degree, and the `A∞` category
`TauCeti.DGCategory.toAInfinityCategory` on it has

* `m₁` the differential of the Hom complexes;
* `m₂(g, f) = g ∘ f`, composition in Keller's order;
* `mₙ = 0` for `n ≥ 3`.

Composition in a `TauCeti.DGCategory` is in Mathlib's enriched factor order, `dgComp f g` being
`f` followed by `g`.  The two orders differ by the Koszul sign: for `f` of degree `p` and `g` of
degree `q`, `g ∘ f = (-1) ^ (p * q) • dgComp f g`.  With this sign the Leibniz rule of the Hom
complexes is the arity-two Stasheff identity `d (g ∘ f) = d g ∘ f + (-1) ^ |g| g ∘ d f`.

The structure is built on the total module of morphisms `⨁ (X, Y), Hom(X, Y)`, on which
Keller-ordered composition, extended by zero on pairs of morphisms which are not composable, is a
nonunital differential graded algebra.  Its `A∞` algebra
(`TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra`) is path-compatible, hence an `A∞` category.
The identities of `C` are not used.

## Main definitions

* `TauCeti.DGCategory.gradedLinearQuiver`: the graded linear quiver of a DG category.
* `TauCeti.DGCategory.homLof`: the inclusion of the morphisms of degree `n` into a hom module.
* `TauCeti.DGCategory.toAInfinityCategory`: the `A∞` category of a DG category.

## Main results

* `TauCeti.DGCategory.homDifferential_toAInfinityCategory_homLof`: the differential `m₁` is the
  differential of the Hom complexes.
* `TauCeti.DGCategory.comp_toAInfinityCategory_homLof`: the composition `m₂` is Keller-ordered
  composition, with the Koszul sign `(-1) ^ (p * q)` relative to `TauCeti.dgComp`.
* `TauCeti.DGCategory.toAInfinityCategory_m_of_three_le`: the operations of arity at least three
  vanish.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open DirectSum

namespace TauCeti

open GradedLinearQuiver

universe v u

namespace DGCategory

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The **graded linear quiver of a differential graded category**: the hom module from `X` to
`Y` is the direct sum `⨁ n, Hom^n(X, Y)` of the morphisms of each degree, graded by the degree
of a morphism. -/
noncomputable instance gradedLinearQuiver : GradedLinearQuiver.{u, v, v} R C :=
  GradedLinearQuiver.ofGradedHom R fun X Y ↦ (dgHomComplex R X Y).X

variable {R C}

/-- The inclusion of the morphisms of degree `n` from `X` to `Y` into the hom module of the
graded linear quiver of a differential graded category. -/
noncomputable def homLof (X Y : C) (n : ℤ) : DGHom R n X Y →ₗ[R] homModule (R := R) X Y :=
  DirectSum.lof R ℤ (fun n ↦ DGHom R n X Y) n

/-- The morphisms of degree `n` in the graded linear quiver of a differential graded category are
the morphisms of degree `n` of the category. -/
theorem grading_piece (X Y : C) (n : ℤ) :
    (grading (R := R) X Y).piece n = LinearMap.range (homLof X Y n) :=
  InternalGrading.ofGradedObject_piece R _ n

/-- A morphism of degree `n` of a differential graded category has degree `n` in its graded linear
quiver. -/
theorem homLof_mem_piece {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    homLof X Y n f ∈ (grading (R := R) X Y).piece n := by
  rw [grading_piece]
  exact LinearMap.mem_range_self _ f

/-- Induction on the hom module of the graded linear quiver of a differential graded category:
a property closed under sums and holding on homogeneous morphisms holds everywhere. -/
@[elab_as_elim]
theorem homModule_induction {X Y : C} {P : homModule (R := R) X Y → Prop} (zero : P 0)
    (add : ∀ f g, P f → P g → P (f + g)) (homLof : ∀ n f, P (homLof X Y n f))
    (f : homModule (R := R) X Y) : P f :=
  DirectSum.induction_on f zero (fun n f ↦ homLof n f) add

/-! ### Keller-ordered composition on hom modules -/

/-- Keller-ordered composition of homogeneous morphisms, as a bilinear map. -/
private noncomputable def kellerCompHom (X Y Z : C) (q p : ℤ) :
    DGHom R q Y Z →ₗ[R] DGHom R p X Y →ₗ[R] homModule (R := R) X Z :=
  LinearMap.mk₂ R (fun g f ↦ homLof X Z (p + q) ((p * q).negOnePow • dgComp R f g rfl))
    (fun g g' f ↦ by rw [dgComp_add, smul_add, map_add])
    (fun r g f ↦ by rw [dgComp_smul, smul_comm, map_smul])
    (fun g f f' ↦ by rw [add_dgComp, smul_add, map_add])
    (fun r g f ↦ by rw [smul_dgComp, smul_comm, map_smul])

/-- Keller-ordered composition `g ∘ f` on the hom modules of the graded linear quiver of a
differential graded category. -/
private noncomputable def kellerComp (X Y Z : C) :
    homModule (R := R) Y Z →ₗ[R] homModule (R := R) X Y →ₗ[R] homModule (R := R) X Z :=
  toModule R ℤ _ fun q ↦ (toModule R ℤ _ fun p ↦ (kellerCompHom X Y Z q p).flip).flip

private theorem kellerComp_homLof_homLof {X Y Z : C} {p q n : ℤ} (g : DGHom R q Y Z)
    (f : DGHom R p X Y) (h : p + q = n) :
    kellerComp X Y Z (homLof Y Z q g) (homLof X Y p f) =
      homLof X Z n ((p * q).negOnePow • dgComp R f g h) := by
  subst h
  simp [kellerComp, homLof, kellerCompHom, homModule_ofGradedHom]

/-- Keller-ordered composition on hom modules is associative. -/
private theorem kellerComp_assoc {W X Y Z : C} (h : homModule (R := R) Y Z)
    (g : homModule (R := R) X Y) (f : homModule (R := R) W X) :
    kellerComp W X Z (kellerComp X Y Z h g) f = kellerComp W Y Z h (kellerComp W X Y g f) := by
  induction h using homModule_induction with
  | zero => simp
  | add h h' ihh ihh' => simp [ihh, ihh']
  | homLof r h =>
  induction g using homModule_induction with
  | zero => simp
  | add g g' ihg ihg' => simp [ihg, ihg']
  | homLof q g =>
  induction f using homModule_induction with
  | zero => simp
  | add f f' ihf ihf' => simp [ihf, ihf']
  | homLof p f =>
  rw [kellerComp_homLof_homLof h g rfl, kellerComp_homLof_homLof g f rfl,
    kellerComp_homLof_homLof _ f (add_assoc p q r).symm,
    kellerComp_homLof_homLof h _ rfl, negOnePow_smul_dgComp_assoc R f g h rfl rfl rfl]

/-- The differential of the hom modules of the graded linear quiver of a differential graded
category: the differential of the Hom complex, applied in every degree. -/
private noncomputable def homDiff (X Y : C) :
    homModule (R := R) X Y →ₗ[R] homModule (R := R) X Y :=
  toModule R ℤ _ fun n ↦ homLof X Y (n + 1) ∘ₗ dgDifferential R n

private theorem homDiff_homLof {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    homDiff X Y (homLof X Y n f) = homLof X Y (n + 1) (dgDifferential R n f) := by
  simp [homDiff, homLof, homModule_ofGradedHom]

/-- The Leibniz rule for Keller-ordered composition on hom modules. -/
private theorem homDiff_kellerComp {X Y Z : C} {q : ℤ} (g : DGHom R q Y Z)
    (f : homModule (R := R) X Y) :
    homDiff X Z (kellerComp X Y Z (homLof Y Z q g) f) =
      kellerComp X Y Z (homDiff Y Z (homLof Y Z q g)) f +
        q.negOnePow • kellerComp X Y Z (homLof Y Z q g) (homDiff X Y f) := by
  induction f using homModule_induction with
  | zero => simp
  | add f f' ihf ihf' => simp only [map_add, ihf, ihf', smul_add]; abel
  | homLof p f =>
  rw [kellerComp_homLof_homLof g f rfl, homDiff_homLof, homDiff_homLof, homDiff_homLof,
    kellerComp_homLof_homLof (dgDifferential R q g) f (add_assoc p q 1).symm,
    kellerComp_homLof_homLof g (dgDifferential R p f) (add_right_comm p 1 q),
    dgDifferential_negOnePow_smul_dgComp, map_add, ← map_zsmul_unit]

private theorem homDiff_homDiff {X Y : C} (f : homModule (R := R) X Y) :
    homDiff X Y (homDiff X Y f) = 0 := by
  induction f using homModule_induction with
  | zero => simp
  | add f f' ihf ihf' => rw [map_add, map_add, ihf, ihf', add_zero]
  | homLof n f => rw [homDiff_homLof, homDiff_homLof, dgDifferential_dgDifferential, map_zero]

/-! ### The total algebra of morphisms -/

/-- Keller-ordered composition on the total module of morphisms: composable pairs compose, and
every other pair of morphisms has product zero. -/
private noncomputable def totalMul : TotalHom R C →ₗ[R] TotalHom R C →ₗ[R] TotalHom R C :=
  letI := Classical.decEq C
  toModule R (C × C) _ fun a ↦ (toModule R (C × C) _ fun b ↦
    (((kellerComp b.1 a.1 a.2).compr₂ (homInclusion b.1 a.2)).compl₂
      (homProjection b.1 a.1 ∘ₗ homInclusion b.1 b.2)).flip).flip

private theorem totalMul_homInclusion_homInclusion {X Y' Y Z : C} (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y') :
    totalMul (homInclusion Y Z g) (homInclusion X Y' f) =
      homInclusion X Z (kellerComp X Y Z g (homProjection X Y (homInclusion X Y' f))) := by
  let := Classical.decEq C
  conv_lhs => rw [homInclusion_eq_lof Y Z, homInclusion_eq_lof X Y']
  simp [totalMul]

private theorem totalMul_homInclusion_self {X Y Z : C} (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) :
    totalMul (homInclusion Y Z g) (homInclusion X Y f) =
      homInclusion X Z (kellerComp X Y Z g f) := by
  rw [totalMul_homInclusion_homInclusion, homProjection_homInclusion]

private theorem totalMul_homInclusion_of_ne {X Y' Y Z : C} (h : Y' ≠ Y)
    (g : homModule (R := R) Y Z) (f : homModule (R := R) X Y') :
    totalMul (homInclusion Y Z g) (homInclusion X Y' f) = 0 := by
  rw [totalMul_homInclusion_homInclusion, homProjection_homInclusion_of_ne (by simp [h]),
    map_zero, map_zero]

/-- Induction on the morphisms of degree `p` in the total module: a property closed under sums and
holding on the morphisms of degree `p` of every hom module holds on every element of degree
`p`. -/
private theorem piece_induction {p : ℤ} {P : TotalHom R C → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (homInclusion : ∀ X Y (f : DGHom R p X Y), P (homInclusion X Y (homLof X Y p f)))
    {x : TotalHom R C} (hx : x ∈ (totalGrading R C).piece p) : P x := by
  refine totalGrading_piece_induction zero add (fun X Y f hf ↦ ?_) hx
  rw [grading_piece] at hf
  obtain ⟨f, rfl⟩ := hf
  exact homInclusion X Y f

private theorem totalMul_assoc (x y z : TotalHom R C) :
    totalMul (totalMul x y) z = totalMul x (totalMul y z) := by
  induction x using totalHom_induction with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | homInclusion Y₂ Z h =>
  induction y using totalHom_induction with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy']
  | homInclusion X₂ Y₁ g =>
  induction z using totalHom_induction with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | homInclusion W X₁ f =>
  by_cases hY : Y₁ = Y₂
  · subst hY
    by_cases hX : X₁ = X₂
    · subst hX
      rw [totalMul_homInclusion_self, totalMul_homInclusion_self, totalMul_homInclusion_self,
        totalMul_homInclusion_self, kellerComp_assoc]
    · rw [totalMul_homInclusion_self, totalMul_homInclusion_of_ne hX,
        totalMul_homInclusion_of_ne hX, map_zero]
  · rw [totalMul_homInclusion_of_ne hY, map_zero, LinearMap.zero_apply]
    by_cases hX : X₁ = X₂
    · subst hX
      rw [totalMul_homInclusion_self, totalMul_homInclusion_of_ne hY]
    · rw [totalMul_homInclusion_of_ne hX, map_zero]

/-- The differential of the total module of morphisms, applied in every hom module. -/
private noncomputable def totalDiff : TotalHom R C →ₗ[R] TotalHom R C :=
  DirectSum.lmap fun a ↦ homDiff a.1 a.2

private theorem totalDiff_homInclusion {X Y : C} (f : homModule (R := R) X Y) :
    totalDiff (homInclusion X Y f) = homInclusion X Y (homDiff X Y f) := by
  let := Classical.decEq C
  rw [homInclusion_eq_lof, totalDiff, DirectSum.lmap_lof]

/-- The total module of morphisms is a nonunital ring under Keller-ordered composition. -/
private noncomputable abbrev totalNonUnitalRing : NonUnitalRing (TotalHom R C) where
  __ := (inferInstance : AddCommGroup (TotalHom R C))
  mul x y := totalMul x y
  left_distrib x y z := map_add (totalMul x) y z
  right_distrib x y z := LinearMap.map_add₂ totalMul x y z
  zero_mul x := LinearMap.map_zero₂ totalMul x
  mul_zero x := map_zero (totalMul x)
  mul_assoc := totalMul_assoc

section TotalAlgebra

attribute [local instance] totalNonUnitalRing

private theorem mul_eq_totalMul (x y : TotalHom R C) : x * y = totalMul x y :=
  (rfl)

private theorem totalIsScalarTower : IsScalarTower R (TotalHom R C) (TotalHom R C) :=
  ⟨fun r x y ↦ by simp only [smul_eq_mul, mul_eq_totalMul, map_smul, LinearMap.smul_apply]⟩

private theorem totalSMulCommClass : SMulCommClass R (TotalHom R C) (TotalHom R C) :=
  ⟨fun r x y ↦ by simp only [smul_eq_mul, mul_eq_totalMul, map_smul]⟩

private theorem totalGradedMul : SetLike.GradedMul (totalGrading R C).piece where
  mul_mem {i j x y} hx hy := by
    refine piece_induction (P := fun x ↦ x * y ∈ (totalGrading R C).piece (i + j))
      (by simp) (fun x x' hx hx' ↦ by rw [add_mul]; exact add_mem hx hx') (fun Y Z g ↦ ?_) hx
    refine piece_induction (P := fun y ↦ homInclusion Y Z (homLof Y Z i g) * y ∈
        (totalGrading R C).piece (i + j))
      (by simp) (fun y y' hy hy' ↦ by rw [mul_add]; exact add_mem hy hy') (fun X Y' f ↦ ?_) hy
    by_cases h : Y' = Y
    · subst h
      rw [mul_eq_totalMul, totalMul_homInclusion_self, kellerComp_homLof_homLof g f (add_comm j i),
        homInclusion_mem_totalGrading_piece_iff]
      exact homLof_mem_piece _
    · rw [mul_eq_totalMul, totalMul_homInclusion_of_ne h]
      exact zero_mem _

attribute [local instance] totalIsScalarTower totalSMulCommClass totalGradedMul

/-- The total module of morphisms of a differential graded category, with Keller-ordered
composition and the differential of the Hom complexes, is a nonunital differential graded
algebra. -/
private theorem isNonUnitalDGAlgebra :
    IsNonUnitalDGAlgebra (totalGrading R C).piece (totalDiff (R := R) (C := C)) where
  map_mem {p a} ha := by
    refine piece_induction (P := fun a ↦ totalDiff a ∈ (totalGrading R C).piece (p + 1))
      (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy) (fun X Y f ↦ ?_) ha
    rw [totalDiff_homInclusion, homDiff_homLof, homInclusion_mem_totalGrading_piece_iff]
    exact homLof_mem_piece _
  sq_zero a := by
    induction a using totalHom_induction with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | homInclusion X Y f =>
      rw [totalDiff_homInclusion, totalDiff_homInclusion, homDiff_homDiff, map_zero]
  leibniz {p a} ha b := by
    refine piece_induction (P := fun a ↦ ∀ b, totalDiff (a * b) =
        totalDiff a * b + p.negOnePow • (a * totalDiff b))
      (by simp) (fun x y hx hy b ↦ by
        simp only [add_mul, map_add, hx b, hy b, smul_add]
        abel) (fun Y Z g b ↦ ?_) ha b
    induction b using totalHom_induction with
    | zero => simp
    | add x y hx hy =>
      simp only [mul_add, map_add, hx, hy, smul_add]
      abel
    | homInclusion X Y' f =>
      simp only [mul_eq_totalMul, totalDiff_homInclusion]
      by_cases h : Y' = Y
      · subst h
        simp only [totalMul_homInclusion_self, totalDiff_homInclusion, homDiff_kellerComp,
          map_add, map_zsmul_unit]
      · simp only [totalMul_homInclusion_of_ne h, map_zero, smul_zero, add_zero]

variable (R C) in
/-- The **`A∞` category of a differential graded category** `C`: the `A∞` category on the graded
linear quiver of `C` whose differential `m₁` is the differential of the Hom complexes, whose
composition `m₂` is composition in Keller's order, `m₂(g, f) = g ∘ f`, and whose operations of
arity at least three vanish.  It is the `A∞` algebra of the nonunital differential graded algebra
of all morphisms of `C`. -/
noncomputable def toAInfinityCategory : AInfinityCategory R C where
  __ := isNonUnitalDGAlgebra.toAInfinityAlgebra
  grading_eq := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading]
    exact InternalGrading.ext fun p ↦ by rw [InternalGrading.ofDecomposition_piece]
  isPathCompatible_m_of_pos n hn := by
    match n, hn with
    | 1, _ =>
      refine ⟨fun X x ↦ ?_, fun s t x i j hij hne ↦ by omega⟩
      rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, totalDiff_homInclusion]
      -- The endpoints `X (0 : Fin 1).rev.castSucc` and `X (0 : Fin 1).rev.succ` of the single
      -- morphism are `X 0` and `X (Fin.last 1)` by computation on `Fin 2`.
      exact ⟨_, rfl⟩
    | 2, _ =>
      refine ⟨fun X x ↦ ?_, fun s t x i j hij hne ↦ ?_⟩
      · rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, mul_eq_totalMul,
          totalMul_homInclusion_homInclusion]
        -- As in arity one, the endpoints of the composite are `X 0` and `X (Fin.last 2)` by
        -- computation on `Fin 3`.
        exact ⟨_, rfl⟩
      · obtain rfl : i = 0 := Fin.ext (by omega)
        obtain rfl : j = 1 := Fin.ext (by omega)
        rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, mul_eq_totalMul,
          totalMul_homInclusion_of_ne hne]
    | n + 3, _ =>
      rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_add_three]
      exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩

private theorem m_toAInfinityCategory :
    (toAInfinityCategory R C).m = isNonUnitalDGAlgebra.toAInfinityAlgebra.m :=
  (rfl)

private theorem m_one_toAInfinityCategory (x : Fin 1 → TotalHom R C) :
    (toAInfinityCategory R C).m 1 x = totalDiff (x 0) := by
  rw [m_toAInfinityCategory, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply]

private theorem m_two_toAInfinityCategory (x : Fin 2 → TotalHom R C) :
    (toAInfinityCategory R C).m 2 x = totalMul (x 0) (x 1) := by
  rw [m_toAInfinityCategory, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, mul_eq_totalMul]

private theorem m_add_three_toAInfinityCategory (n : ℕ) :
    (toAInfinityCategory R C).m (n + 3) = 0 := by
  rw [m_toAInfinityCategory, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_add_three]

end TotalAlgebra

/-- **The differential of the `A∞` category of a differential graded category** is the
differential of its Hom complexes. -/
@[simp]
theorem homDifferential_toAInfinityCategory_homLof {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (toAInfinityCategory R C).homDifferential X Y (homLof X Y n f) =
      homLof X Y (n + 1) (dgDifferential R n f) := by
  apply homInclusion_injective X Y
  rw [AInfinityCategory.homInclusion_homDifferential, AInfinityAlgebra.differential_apply,
    m_one_toAInfinityCategory, Matrix.cons_val_zero, totalDiff_homInclusion, homDiff_homLof]

/-- **The composition of the `A∞` category of a differential graded category** is composition in
Keller's order: for `g : Y ⟶ Z` of degree `q` and `f : X ⟶ Y` of degree `p`, the composite
`g ∘ f` is the enriched composite `dgComp f g` up to the Koszul sign `(-1) ^ (p * q)`. -/
@[simp]
theorem comp_toAInfinityCategory_homLof {X Y Z : C} {p q : ℤ} (g : DGHom R q Y Z)
    (f : DGHom R p X Y) :
    (toAInfinityCategory R C).comp X Y Z (homLof Y Z q g) (homLof X Y p f) =
      (p * q).negOnePow • homLof X Z (p + q) (dgComp R f g rfl) := by
  apply homInclusion_injective X Z
  rw [AInfinityCategory.homInclusion_comp, m_two_toAInfinityCategory, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero, totalMul_homInclusion_self,
    kellerComp_homLof_homLof g f rfl, map_zsmul_unit]

/-- The operations of arity at least three of the `A∞` category of a differential graded category
vanish. -/
theorem toAInfinityCategory_m_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (toAInfinityCategory R C).m n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact m_add_three_toAInfinityCategory k

/-- The simp-normal form of `toAInfinityCategory_m_of_three_le`. -/
@[simp]
theorem toAInfinityCategory_m_add_three (n : ℕ) : (toAInfinityCategory R C).m (n + 3) = 0 :=
  m_add_three_toAInfinityCategory n

end DGCategory

end TauCeti
