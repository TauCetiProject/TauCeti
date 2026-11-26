/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Curved.Basic
public import TauCeti.CategoryTheory.AInfinity.Unit

/-!
# Strict units and scalar curvature in curved A-infinity categories

A family of **strict units** of a curved `A∞` category `𝒞` is a degree-zero endomorphism `e X` of
every object `X`, which is a two-sided identity for `m₂` and on which every operation of arity
other than two vanishes. This is the definition `TauCeti.AInfinityCategory.StrictUnit` of the
uncurved case; the curvature is not constrained by it.

The curvature has **scalar** type when `m₀(X) = c X • e X` for a scalar `c X`, the *potential* of
`X`. This is the shape of the curvature of a Lagrangian brane deformed by a weak bounding cochain
in Floer theory. A strict unit then removes the curvature from the curved Stasheff identities in
every arity but one. In arity zero, `m₁(m₀(X)) = c X • m₁(e X) = 0`. In arity `n ≥ 2` the
curvature is inserted into the operation `m_{n + 1}` of arity at least three, which vanishes on a
multiple of a unit. In arity one the two insertions are `m₂(c Y • e Y, a) = c Y • a` and
`m₂(a, c X • e X) = c X • a` for `a : X ⟶ Y`, so

`m₁(m₁(a)) = (c X - c Y) • a`.

So the unary operation squares to zero exactly on the morphisms between objects of equal
potential. In particular, if every object has the same potential `c`, then the operations of
positive arity satisfy the uncurved Stasheff identities and form an uncurved `A∞` category with
the same strict units (`TauCeti.CurvedAInfinityCategory.toAInfinityCategoryOfCurvatureEqSmul`):
the category of objects of one fixed potential is uncurved. In Floer theory this is what lets the
unary operation define the Floer cohomology of two branes whose weak bounding cochains have equal
potential.

## Main definitions

* `TauCeti.CurvedAInfinityCategory.StrictUnit`: a family of strict units of a curved `A∞`
  category.
* `TauCeti.CurvedAInfinityCategory.toAInfinityCategoryOfCurvatureEqSmul`: a curved `A∞` category
  whose curvature is a common scalar multiple of a strict unit, as an uncurved one with the same
  operations.

## Main results

* `TauCeti.CurvedAInfinityCategory.strictUnit_iff_of_m_eq`: a curved and an uncurved `A∞`
  category with the same operations have the same strict units.
* `TauCeti.AInfinityCategory.strictUnit_toCurvedAInfinityCategory_iff`: the strict units of an
  uncurved `A∞` category are those of it as a curved one.
* `TauCeti.CurvedAInfinityCategory.StrictUnit.endAlgebra`: a strict unit of `𝒞` at `X` is a strict
  unit of the endomorphism algebra of `X`.
* `TauCeti.CurvedAInfinityCategory.StrictUnit.curvatureInsertionSum_eq_zero_of_ne_one` and
  `TauCeti.CurvedAInfinityCategory.StrictUnit.curvatureInsertionSum_one_eq`: for scalar
  curvature, the curvature insertions vanish in every arity other than one, and in arity one they
  are `(c (X 0) - c (X 1)) • x₀` for `x₀ : X 1 ⟶ X 0`.
* `TauCeti.CurvedAInfinityCategory.StrictUnit.m_one_m_one_of_curvature_eq_smul`: for scalar
  curvature, `m₁(m₁(a)) = (c X - c Y) • a` for `a : X ⟶ Y`.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Sections 3.6 and 3.7,
  for weak bounding cochains, their potential, and the Floer cohomology of a pair of branes of
  equal potential.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.5 and 7.1, for strict
  units.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver AInfinity

namespace CurvedAInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- A family of **strict units** for a curved `A∞` category, as for uncurved ones.

For every object `X`, the endomorphism `e X` has degree zero. These endomorphisms are the left and
right identities for `m₂`, and every operation of arity other than two vanishes on a tuple
containing an included identity. The curvature is not constrained. -/
structure StrictUnit (𝒞 : CurvedAInfinityCategory R C)
    (e : ∀ X : C, homModule (R := R) X X) : Prop where
  /-- Every identity has degree zero. -/
  degree_zero (X : C) : e X ∈ (grading (R := R) X X).piece 0
  /-- The identity at the target is a left identity for `m₂`. -/
  binary_left (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion Y Y (e Y), homInclusion X Y f] = homInclusion X Y f
  /-- The identity at the source is a right identity for `m₂`. -/
  binary_right (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion X Y f, homInclusion X X (e X)] = homInclusion X Y f
  /-- Every operation of arity other than two vanishes on a tuple containing an included
  identity. -/
  higher (n : ℕ) (hn : n ≠ 2) (x : Fin n → TotalHom R C) :
    (∃ i X, x i = homInclusion X X (e X)) → 𝒞.m n x = 0

attribute [simp] StrictUnit.binary_left StrictUnit.binary_right

namespace StrictUnit

variable {𝒞 : CurvedAInfinityCategory R C} {e e' : ∀ X : C, homModule (R := R) X X}

/-- An operation of arity other than two vanishes when one of its inputs is a scalar multiple of
an included strict identity. -/
theorem m_eq_zero_of_eq_smul (h : 𝒞.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → TotalHom R C) {i : Fin n} {X : C} {c : R}
    (hi : x i = c • homInclusion X X (e X)) : 𝒞.m n x = 0 := by
  rw [← Function.update_eq_self i x, hi, (𝒞.m n).map_update_smul,
    h.higher n hn _ ⟨i, X, Function.update_self ..⟩, smul_zero]

/-- An included strict identity is closed under the unary operation. -/
@[simp]
theorem unary_eq_zero (h : 𝒞.StrictUnit e) (X : C) : 𝒞.m 1 ![homInclusion X X (e X)] = 0 :=
  h.higher 1 (by decide) _ ⟨0, X, rfl⟩

/-- Composing on the left with a scalar multiple of the strict identity at the target is scalar
multiplication. -/
theorem m_two_smul_left (h : 𝒞.StrictUnit e) {X Y : C} (c : R) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![c • homInclusion Y Y (e Y), homInclusion X Y f] = c • homInclusion X Y f := by
  have hu (y : TotalHom R C) :
      Function.update ![homInclusion Y Y (e Y), homInclusion X Y f] 0 y =
        ![y, homInclusion X Y f] :=
    Fin.update_cons_zero ..
  rw [← hu, (𝒞.m 2).map_update_smul, hu, h.binary_left, RingHom.id_apply]

/-- Composing on the right with a scalar multiple of the strict identity at the source is scalar
multiplication. -/
theorem m_two_smul_right (h : 𝒞.StrictUnit e) {X Y : C} (c : R) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion X Y f, c • homInclusion X X (e X)] = c • homInclusion X Y f := by
  have hu (y : TotalHom R C) :
      Function.update ![homInclusion X Y f, homInclusion X X (e X)] 1 y =
        ![homInclusion X Y f, y] := by
    ext i
    fin_cases i <;> rfl
  rw [← hu, (𝒞.m 2).map_update_smul, hu, h.binary_right, RingHom.id_apply]

/-- A family of strict identities in a curved `A∞` category is unique. -/
theorem eq (h : 𝒞.StrictUnit e) (h' : 𝒞.StrictUnit e') : e = e' := by
  funext X
  apply homInclusion_injective X X
  calc
    homInclusion X X (e X) = 𝒞.m 2 ![homInclusion X X (e' X), homInclusion X X (e X)] :=
      (h'.binary_left X X (e X)).symm
    _ = homInclusion X X (e' X) := h.binary_right X X (e' X)

/-- **A strict unit restricts to the endomorphism algebras**: the strict identity of `X` is a
strict unit of the curved `A∞` algebra of endomorphisms of `X`. -/
theorem endAlgebra (h : 𝒞.StrictUnit e) (X : C) : (𝒞.endAlgebra X).StrictUnit (e X) where
  degree_zero := by simpa using h.degree_zero X
  binary_left f := homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X two_pos]
    convert h.binary_left X X f using 2
    ext i
    fin_cases i <;> rfl
  binary_right f := homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X two_pos]
    convert h.binary_right X X f using 2
    ext i
    fin_cases i <;> rfl
  higher n hn y := fun ⟨i, hi⟩ ↦ homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X (Fin.pos i), map_zero]
    exact h.higher n hn _ ⟨i, X, by rw [hi]⟩

/-! ### Scalar curvature -/

variable {c : C → R}

/-- **The curvature insertions of scalar curvature vanish outside arity one.** If the curvature of
every object `X` is `c X • e X`, then on a string through the objects `X 0, X 1, …` the
curvature insertions of every arity `n ≠ 1` vanish: in arity zero the unit is a cycle, and in
arity `n ≥ 2` it is inserted into an operation of arity at least three. -/
theorem curvatureInsertionSum_eq_zero_of_ne_one (h : 𝒞.StrictUnit e)
    (hc : ∀ X, 𝒞.curvature X = c X • e X) (X : ℕ → C) (x : ℕ → TotalHom R C) {n : ℕ}
    (hn : n ≠ 1) :
    curvatureInsertionSum 𝒞.m x (fun p ↦ homInclusion (X p) (X p) (𝒞.curvature (X p))) n =
      0 := by
  rw [curvatureInsertionSum_def]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  rw [MultilinearMap.evalNat_def,
    h.m_eq_zero_of_eq_smul (by omega) _ (i := ⟨p, Finset.mem_range.1 hp⟩) (X := X p)
      (c := c (X p)) (by simp [hc]), smul_zero]

/-- **The curvature insertions of scalar curvature in arity one.** If the curvature of every
object `X` is `c X • e X`, then for `x₀ : X 1 ⟶ X 0` the curvature insertions of arity one are
`m₂(m₀(X 0), x₀) - m₂(x₀, m₀(X 1)) = (c (X 0) - c (X 1)) • x₀`. -/
theorem curvatureInsertionSum_one_eq (h : 𝒞.StrictUnit e) (hc : ∀ X, 𝒞.curvature X = c X • e X)
    (X : ℕ → C) {x : ℕ → TotalHom R C}
    (hx : x 0 ∈ LinearMap.range (homInclusion (R := R) (X 1) (X 0))) :
    curvatureInsertionSum 𝒞.m x (fun p ↦ homInclusion (X p) (X p) (𝒞.curvature (X p))) 1 =
      (c (X 0) - c (X 1)) • x 0 := by
  obtain ⟨f, hf⟩ := hx
  rw [curvatureInsertionSum_one, hc, hc, map_smul, map_smul, ← hf, h.m_two_smul_left,
    h.m_two_smul_right, sub_smul]

/-- **The unary operation under scalar curvature.** If the curvature of every object `X` is
`c X • e X` for a strict unit `e`, then the unary operation squares to `(c X - c Y) • a` on every
morphism `a : X ⟶ Y`. In particular it squares to zero on the morphisms between objects of equal
potential. -/
theorem m_one_m_one_of_curvature_eq_smul (h : 𝒞.StrictUnit e)
    (hc : ∀ X, 𝒞.curvature X = c X • e X) {X Y : C} (f : homModule (R := R) X Y) :
    𝒞.m 1 ![𝒞.m 1 ![homInclusion X Y f]] = (c X - c Y) • homInclusion X Y f := by
  rw [𝒞.m_one_m_one, hc, hc, map_smul, map_smul, h.m_two_smul_left, h.m_two_smul_right, sub_smul]

end StrictUnit

/-! ### Comparison with uncurved strict units -/

/-- The strict units of a curved `A∞` category are those of any uncurved `A∞` category with the
same operations: both notions only read the operations on the total module of morphisms. -/
theorem strictUnit_iff_of_m_eq {𝒞 : AInfinityCategory R C} {𝒟 : CurvedAInfinityCategory R C}
    (hm : 𝒟.m = 𝒞.m) {e : ∀ X : C, homModule (R := R) X X} :
    𝒟.StrictUnit e ↔ 𝒞.StrictUnit e := by
  have hl (X Y : C) (f : homModule (R := R) X Y) :
      𝒞.comp X Y Y (e Y) f = f ↔ 𝒟.m 2 ![homInclusion Y Y (e Y), homInclusion X Y f] =
        homInclusion X Y f := by
    rw [hm, ← 𝒞.homInclusion_comp, (homInclusion_injective X Y).eq_iff]
  have hr (X Y : C) (f : homModule (R := R) X Y) :
      𝒞.comp X X Y f (e X) = f ↔ 𝒟.m 2 ![homInclusion X Y f, homInclusion X X (e X)] =
        homInclusion X Y f := by
    rw [hm, ← 𝒞.homInclusion_comp, (homInclusion_injective X Y).eq_iff]
  refine ⟨fun h ↦ ⟨h.degree_zero, fun X Y f ↦ (hl X Y f).2 (h.binary_left X Y f),
    fun X Y f ↦ (hr X Y f).2 (h.binary_right X Y f), fun n hn x hx ↦ hm ▸ h.higher n hn x hx⟩,
    fun h ↦ ⟨h.degree_zero, fun X Y f ↦ (hl X Y f).1 (h.binary_left X Y f),
      fun X Y f ↦ (hr X Y f).1 (h.binary_right X Y f), fun n hn x hx ↦ hm ▸ h.higher n hn x hx⟩⟩

/-! ### The category of one fixed potential -/

variable (𝒞 : CurvedAInfinityCategory R C) {e : ∀ X : C, homModule (R := R) X X}

/-- If every curvature is `c • e X` for one scalar `c` and a strict unit `e`, the Stasheff
identities of the operations of positive arity hold on all homogeneous inputs: on a composable
string the curvature insertions vanish. -/
private theorem stasheffSum_eq_zero_of_curvature_eq_smul (h : 𝒞.StrictUnit e) {c : R}
    (hc : ∀ X, 𝒞.curvature X = c • e X) (n : ℕ) (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → TotalHom R C)
    (hx : ∀ i < n, x i ∈ (totalGrading R C).piece (d i)) : stasheffSum 𝒞.m d x n = 0 := by
  refine stasheffSum_eq_zero_of_isPathCompatible 𝒞.m_degree 𝒞.isPathCompatible_m_of_pos hn
    (fun X d' y hy hd' ↦ ?_) d x hx
  have hs := 𝒞.stasheff n X d' y hy hd'
  rcases eq_or_ne n 1 with rfl | hn₁
  · rwa [h.curvatureInsertionSum_one_eq (c := fun _ ↦ c) hc X (hy 0 Nat.zero_lt_one), sub_self,
      zero_smul, add_zero] at hs
  · rwa [h.curvatureInsertionSum_eq_zero_of_ne_one (c := fun _ ↦ c) hc X y hn₁, add_zero] at hs

/-- **The category of one fixed potential is uncurved.** A curved `A∞` category whose curvature
is `c • e X` at every object `X`, for one scalar `c` and a strict unit `e`, is an uncurved `A∞`
category with the same operations of positive arity; its Taylor map is the suspension of the
operations. Its strict units are those of `𝒞`
(`TauCeti.CurvedAInfinityCategory.strictUnit_toAInfinityCategoryOfCurvatureEqSmul`). -/
noncomputable def toAInfinityCategoryOfCurvatureEqSmul (h : 𝒞.StrictUnit e) (c : R)
    (hc : ∀ X, 𝒞.curvature X = c • e X) : AInfinityCategory R C where
  toAInfinityAlgebra := AInfinityAlgebra.ofStasheff (totalGrading R C) 𝒞.m 𝒞.m_zero 𝒞.m_degree
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (𝒞.stasheffSum_eq_zero_of_curvature_eq_smul h hc)
  grading_eq := AInfinityAlgebra.ofStasheff_grading ..
  isPathCompatible_m_of_pos n hn := by
    rw [AInfinityAlgebra.ofStasheff_m]
    exact 𝒞.isPathCompatible_m_of_pos n hn

/-- The uncurved `A∞` category of one fixed potential has the operations of `𝒞`. -/
@[simp]
theorem toAInfinityCategoryOfCurvatureEqSmul_m (h : 𝒞.StrictUnit e) (c : R)
    (hc : ∀ X, 𝒞.curvature X = c • e X) :
    (𝒞.toAInfinityCategoryOfCurvatureEqSmul h c hc).m = 𝒞.m :=
  AInfinityAlgebra.ofStasheff_m ..

variable {𝒞} in
/-- The uncurved `A∞` category of one fixed potential has the strict units of `𝒞`. -/
theorem strictUnit_toAInfinityCategoryOfCurvatureEqSmul (h : 𝒞.StrictUnit e) (c : R)
    (hc : ∀ X, 𝒞.curvature X = c • e X) :
    (𝒞.toAInfinityCategoryOfCurvatureEqSmul h c hc).StrictUnit e :=
  (strictUnit_iff_of_m_eq (toAInfinityCategoryOfCurvatureEqSmul_m ..).symm).1 h

end CurvedAInfinityCategory

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- The strict units of an uncurved `A∞` category are those of it as a curved one. -/
@[simp]
theorem strictUnit_toCurvedAInfinityCategory_iff {𝒞 : AInfinityCategory R C}
    {e : ∀ X : C, homModule (R := R) X X} :
    𝒞.toCurvedAInfinityCategory.StrictUnit e ↔ 𝒞.StrictUnit e :=
  CurvedAInfinityCategory.strictUnit_iff_of_m_eq 𝒞.toCurvedAInfinityCategory_m

/-- A strict unit of an uncurved `A∞` category is a strict unit of it as a curved one. -/
theorem StrictUnit.toCurvedAInfinityCategory {𝒞 : AInfinityCategory R C}
    {e : ∀ X : C, homModule (R := R) X X} (h : 𝒞.StrictUnit e) :
    𝒞.toCurvedAInfinityCategory.StrictUnit e :=
  strictUnit_toCurvedAInfinityCategory_iff.2 h

end AInfinityCategory

end TauCeti
