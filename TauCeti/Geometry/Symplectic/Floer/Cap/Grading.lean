/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Action
public import TauCeti.Geometry.Symplectic.Floer.Cap.ConleyZehnder

/-!
# The Conley–Zehnder index of raw caps and cap classes

Let `γ` be a loop based at `x` in a Hausdorff σ-compact manifold `M` with a fiberwise
nondegenerate two-form `σ`, such as a contractible one-periodic orbit of a Hamiltonian on a closed
symplectic manifold, and let `Φ(t) : T_(γ 0) M ≃ T_(γ t) M` be a continuous family of linear maps
preserving `σ`, such as the linearized flow along the orbit. For a smooth based cap `u` of `γ`, the
Conley–Zehnder index of `Φ` along the capped loop `(γ, u)` is
`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex`. This file shows that it is a function of the
raw cap of `u` (`TauCeti.Floer.RawCap γ`, a homotopy class of discs bounding `γ`), extends it to
all raw caps of `γ`, and descends it to the cap classes `TauCeti.Floer.SphericalCapClass ω c γ` of
capped Hamiltonian Floer theory. At a nondegenerate orbit the index is an integer, the grading of
the capped orbit.

* **Raw caps.** Once `γ` has one smooth based cap, the index extends to all raw caps of `γ`
  (`TauCeti.Floer.RawCap.conleyZehnderIndex`). On the raw cap of every smooth based cap `u` it is
  the index along `(γ, u)` (`TauCeti.Floer.RawCap.conleyZehnderIndex_homotopyClass`), and gluing a
  sphere `a ∈ π₂(M, x)` to a raw cap lowers it by twice the first Chern number of `a`
  (`TauCeti.Floer.RawCap.conleyZehnderIndex_vadd`).
* **Cap classes.** Let `ω` and `c` be homomorphisms on `H₂(M; ℤ)` defining the period group
  `Γ = SphericalPeriodGroup ω c`, with `c` the first Chern number on spherical classes: `c` of the
  Hurewicz class of every sphere `a` is `c₁(a)`. Such a `c` exists
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_addMonoidHom_hurewiczIntHom_eq_firstChernHom`).
  Then the index descends to the cap classes of `γ`
  (`TauCeti.Floer.SphericalCapClass.conleyZehnderIndex`), and recapping a cap class by `B ∈ Γ`
  lowers it by the degree `2 c₁(B)` of `B`
  (`TauCeti.Floer.SphericalCapClass.conleyZehnderIndex_vadd`).
  Two cap classes have the same index exactly when the class by which they differ has first Chern
  number zero (`TauCeti.Floer.SphericalCapClass.conleyZehnderIndex_eq_conleyZehnderIndex_iff`), so
  a cap class is determined by its capped action and its Conley–Zehnder index
  (`TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_conleyZehnderIndex_eq`): the two
  invariants of a capped orbit separate the cap classes, as the joint kernel defining `Γ`
  requires.
* **Integrality.** Suppose that `Φ` starts at the identity and that its endpoint `Φ(1)` fixes no
  nonzero vector, as the linearized flow along a nondegenerate one-periodic orbit does. In a
  periodic symplectic frame along `γ`, `Φ` becomes a path of linear symplectic maps from the
  identity to a map without the eigenvalue `1`, whose index is an integer
  (`TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq_of_one`). Hence the index of every
  smooth cap, raw cap and cap class of `γ` is an integer
  (`TauCeti.SmoothTwoForm.exists_int_frameConleyZehnderIndex_eq`,
  `TauCeti.Floer.IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq`,
  `TauCeti.Floer.RawCap.exists_int_conleyZehnderIndex_eq`,
  `TauCeti.Floer.SphericalCapClass.exists_int_conleyZehnderIndex_eq`).
* **The grading.** The grading of a cap class `TauCeti.Floer.SphericalCapClass.grading` is the
  nearest integer to its index, which is the index itself at a nondegenerate orbit
  (`TauCeti.Floer.SphericalCapClass.grading_eq`). Recapping by `B ∈ Γ` lowers it by `2 c₁(B)`
  (`TauCeti.Floer.SphericalCapClass.grading_vadd`) for every `Φ`, and a cap class is determined by
  its capped action and its grading
  (`TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_grading_eq`).

## Sign convention

Recapping by `B` lowers both the Conley–Zehnder index, by `2 c₁(B)`, and the capped action, by the
area of `B` (`TauCeti.Floer.SphericalCapClass.action_vadd`), so the index moves with the action, as
the grading of capped Hamiltonian Floer theory does. In the sign convention of
`TauCeti.SymplecticForm.conleyZehnderIndex`, which reads paths in bases in which the symplectic
form has the matrix `Matrix.J`, the index is therefore the grading `μ` itself, not its negative.
This agrees with the normalization of `μ` at the constant orbits of a small Morse Hamiltonian
`ε F`, whose index is `ind_p(F) - n`
(`exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`).
The convention `μ = -CZ` refers to the index read in complex coordinates, which has the opposite
sign.

## Main definitions

* `TauCeti.Floer.RawCap.conleyZehnderIndex`: the Conley–Zehnder index of a raw cap.
* `TauCeti.Floer.SphericalCapClass.conleyZehnderIndex`: the Conley–Zehnder index of a cap class.
* `TauCeti.Floer.SphericalCapClass.grading`: the grading of a cap class.

## Main results

* `TauCeti.Floer.RawCap.conleyZehnderIndex_homotopyClass`: on the raw cap of a smooth based cap
  it is the index of the smooth cap.
* `TauCeti.Floer.RawCap.conleyZehnderIndex_vadd`,
  `TauCeti.Floer.SphericalCapClass.conleyZehnderIndex_vadd`: the recapping laws.
* `TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_conleyZehnderIndex_eq`: a cap class is
  determined by its action and its Conley–Zehnder index.
* `TauCeti.Floer.RawCap.exists_int_conleyZehnderIndex_eq`,
  `TauCeti.Floer.SphericalCapClass.exists_int_conleyZehnderIndex_eq`: integrality at a
  nondegenerate orbit.
* `TauCeti.Floer.SphericalCapClass.grading_eq`, `TauCeti.Floer.SphericalCapClass.grading_vadd`,
  `TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_grading_eq`: the grading is the index at a
  nondegenerate orbit, its recapping law, and the separation of cap classes.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index of a capped periodic orbit and
  its change under recapping).
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524 (the grading of capped orbits).
-/

public section

noncomputable section

open Set CategoryTheory HomotopyGroup
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti.Floer

open SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ### The Conley–Zehnder index of a raw cap -/

namespace RawCap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  {σ : SmoothTwoForm I M} {x : M} {γ : Ω M x}
  {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}

/-- The **Conley–Zehnder index of a raw cap** `D` of a loop `γ` with a smooth based cap `u₀`, for a
fiberwise nondegenerate two-form `σ` and a continuous family `Φ` of linear maps along `γ`
preserving `σ`: the index of `Φ` along the capped loop `(γ, u₀)` minus twice the first Chern number
of the sphere `D -ᵥ u₀.homotopyClass` by which `D` differs from the raw cap of `u₀`. It is defined
only for loops that have a smooth based cap. On the raw cap of every smooth based cap `u` it is the
index along `(γ, u)` (`TauCeti.Floer.RawCap.conleyZehnderIndex_homotopyClass`), so it does not
depend on `u₀`. -/
def conleyZehnderIndex (h : σ.IsNondegenerate) (hcap : ∃ u, IsSmoothBasedCap I γ u)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) (D : RawCap γ) : ℝ :=
  hcap.choose_spec.conleyZehnderIndex h hΦ hΦσ -
    2 * (h.firstChernHom x (D -ᵥ hcap.choose_spec.homotopyClass) : ℝ)

variable (h : σ.IsNondegenerate) (hcap : ∃ u, IsSmoothBasedCap I γ u)
  (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
    (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
  (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v)

/-- The defining equation of `TauCeti.Floer.RawCap.conleyZehnderIndex`. -/
theorem conleyZehnderIndex_def (D : RawCap γ) :
    conleyZehnderIndex h hcap hΦ hΦσ D = hcap.choose_spec.conleyZehnderIndex h hΦ hΦσ -
      2 * (h.firstChernHom x (D -ᵥ hcap.choose_spec.homotopyClass) : ℝ) :=
  (rfl)

/-- **The index of a smooth cap.** The Conley–Zehnder index of the raw cap of a smooth based cap
`u` of `γ` is the Conley–Zehnder index of `Φ` along the capped loop `(γ, u)`. -/
theorem conleyZehnderIndex_homotopyClass {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    conleyZehnderIndex h hcap hΦ hΦσ hu.homotopyClass = hu.conleyZehnderIndex h hΦ hΦσ := by
  rw [conleyZehnderIndex_def,
    hcap.choose_spec.conleyZehnderIndex_eq_sub_two_mul_firstChernHom h hu hΦ hΦσ]

/-- **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap, with the orientation of the
cap, lowers its Conley–Zehnder index by twice the first Chern number of `a`. -/
theorem conleyZehnderIndex_vadd (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    conleyZehnderIndex h hcap hΦ hΦσ (a +ᵥ D) =
      -2 * (h.firstChernHom x a : ℝ) + conleyZehnderIndex h hcap hΦ hΦσ D := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, vadd_vsub_assoc, map_add, Int.cast_add]
  ring

/-- **Two raw caps differ by a sphere.** The Conley–Zehnder indices of two raw caps of `γ` differ by
minus twice the first Chern number of the sphere by which they differ. -/
theorem conleyZehnderIndex_sub_conleyZehnderIndex (D' D : RawCap γ) :
    conleyZehnderIndex h hcap hΦ hΦσ D' - conleyZehnderIndex h hcap hΦ hΦσ D =
      -2 * (h.firstChernHom x (D' -ᵥ D) : ℝ) := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  conv_lhs => rw [← vsub_vadd D' D, conleyZehnderIndex_vadd]
  ring

/-- **The index of a raw cap of a nondegenerate orbit is an integer.** If the family `Φ` starts at
the identity and its endpoint `Φ(1)` fixes no nonzero vector, as the linearized flow along a
nondegenerate periodic orbit does, the Conley–Zehnder index of every raw cap of `γ` is an
integer. -/
theorem exists_int_conleyZehnderIndex_eq (hΦ₀ : ∀ v, Φ 0 v = v) (hΦ₁ : ∀ v, Φ 1 v = v → v = 0)
    (D : RawCap γ) : ∃ k : ℤ, conleyZehnderIndex h hcap hΦ hΦσ D = k := by
  obtain ⟨k, hk⟩ := hcap.choose_spec.exists_int_conleyZehnderIndex_eq h hΦ hΦσ hΦ₀ hΦ₁
  refine ⟨k - 2 * h.firstChernHom x (D -ᵥ hcap.choose_spec.homotopyClass), ?_⟩
  rw [conleyZehnderIndex_def, hk]
  push_cast
  ring

end RawCap

/-! ### The Conley–Zehnder index of a cap class -/

namespace SphericalCapClass

open AlgebraicTopology

-- `ω` names the area homomorphism here, so the `ContDiff` scope, whose notation includes `ω`, is
-- not opened, and smoothness `∞` is written out.
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  {σ : SmoothTwoForm I M} {x : M} {γ : Ω M x}
  {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ}

/-- The **Conley–Zehnder index of a cap class**, for a fiberwise nondegenerate two-form `σ`, a
continuous family `Φ` of linear maps along `γ` preserving `σ`, and a homomorphism `c` on
`H₂(M; ℤ)` that is the first Chern number of `σ` on the Hurewicz classes of spheres (`hc`): the
Conley–Zehnder index `TauCeti.Floer.RawCap.conleyZehnderIndex` of any raw cap in the class. It is
well defined because raw caps in the same class differ by a sphere whose Hurewicz class has zero
`c`, hence zero first Chern number. -/
def conleyZehnderIndex (h : σ.IsNondegenerate)
    (hc : ∀ a, c (hurewiczIntHom M x 1 a) = h.firstChernHom x a)
    (hcap : ∃ u, IsSmoothBasedCap I γ u)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    SphericalCapClass ω c γ → ℝ :=
  lift (-(Int.castAddHom ℝ).comp (PeriodGroup.degree _ _))
    (RawCap.conleyZehnderIndex h hcap hΦ hΦσ) fun a D ↦ by
      simp [RawCap.conleyZehnderIndex_vadd, PeriodGroup.degree_apply,
        SphericalPeriodGroup.chern_ofHomotopyGroup, hc]

variable (h : σ.IsNondegenerate) (hc : ∀ a, c (hurewiczIntHom M x 1 a) = h.firstChernHom x a)
  (hcap : ∃ u, IsSmoothBasedCap I γ u)
  (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
    (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
  (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v)

/-- The Conley–Zehnder index of the cap class of a raw cap is the index of the raw cap. -/
@[simp]
theorem conleyZehnderIndex_mk (D : RawCap γ) :
    conleyZehnderIndex h hc hcap hΦ hΦσ (mk ω c D) = RawCap.conleyZehnderIndex h hcap hΦ hΦσ D :=
  lift_mk _ _ _ D

/-- **Two cap classes differ by a class of the period group.** The Conley–Zehnder indices of two
cap classes of `γ` differ by minus the degree `2 c₁` of the class by which they differ. -/
theorem conleyZehnderIndex_sub_conleyZehnderIndex (q' q : SphericalCapClass ω c γ) :
    conleyZehnderIndex h hc hcap hΦ hΦσ q' - conleyZehnderIndex h hc hcap hΦ hΦσ q =
      -(PeriodGroup.degree _ _ (q' -ᵥ q) : ℝ) := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D =>
    rw [conleyZehnderIndex_mk, conleyZehnderIndex_mk, mk_vsub_mk, PeriodGroup.degree_apply,
      SphericalPeriodGroup.chern_ofHomotopyGroup, hc,
      RawCap.conleyZehnderIndex_sub_conleyZehnderIndex]
    push_cast
    ring

/-- Two cap classes of `γ` have the same Conley–Zehnder index exactly when the class of the period
group by which they differ has first Chern number zero. -/
theorem conleyZehnderIndex_eq_conleyZehnderIndex_iff {q' q : SphericalCapClass ω c γ} :
    conleyZehnderIndex h hc hcap hΦ hΦσ q' = conleyZehnderIndex h hc hcap hΦ hΦσ q ↔
      PeriodGroup.chern _ _ (q' -ᵥ q) = 0 := by
  rw [← sub_eq_zero, conleyZehnderIndex_sub_conleyZehnderIndex, neg_eq_zero,
    PeriodGroup.degree_apply, Int.cast_eq_zero, mul_eq_zero]
  simp

/-- **A cap class is determined by its action and its Conley–Zehnder index.** For a closed `C¹`
two-form `α` whose integral over every sphere is the value of `ω` on its Hurewicz class, for
instance `σ` itself when `ω` is its area, and any Hamiltonian `Ham`, two cap classes of `γ` are
equal exactly when they have the same capped action and the same Conley–Zehnder index. -/
theorem eq_iff_action_eq_and_conleyZehnderIndex_eq [CompactSpace M] [I.Boundaryless]
    {α : RoughForm I M ℝ 2} {hα : IsSmoothForm I 1 α} {hdα : mextDeriv α = 0}
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hα hdα a) (Ham : ℝ → M → ℝ)
    {q' q : SphericalCapClass ω c γ} :
    q' = q ↔ action hα hdα hω Ham hcap q' = action hα hdα hω Ham hcap q ∧
      conleyZehnderIndex h hc hcap hΦ hΦσ q' = conleyZehnderIndex h hc hcap hΦ hΦσ q := by
  rw [conleyZehnderIndex_eq_conleyZehnderIndex_iff, eq_iff_action_eq_and_chern_vsub_eq_zero hω]

/-- **The index of a cap class of a nondegenerate orbit is an integer.** If the family `Φ` starts
at the identity and its endpoint `Φ(1)` fixes no nonzero vector, as the linearized flow along a
nondegenerate periodic orbit does, the Conley–Zehnder index of every cap class of `γ` is an
integer. -/
theorem exists_int_conleyZehnderIndex_eq (hΦ₀ : ∀ v, Φ 0 v = v) (hΦ₁ : ∀ v, Φ 1 v = v → v = 0)
    (q : SphericalCapClass ω c γ) : ∃ k : ℤ, conleyZehnderIndex h hc hcap hΦ hΦσ q = k := by
  induction q using induction_on with
  | h D =>
    rw [conleyZehnderIndex_mk]
    exact RawCap.exists_int_conleyZehnderIndex_eq h hcap hΦ hΦσ hΦ₀ hΦ₁ D

/-- The **grading** of a cap class: the nearest integer to its Conley–Zehnder index. When `Φ`
starts at the identity and `Φ(1)` fixes no nonzero vector, as for the linearized flow along a
nondegenerate one-periodic orbit, it is the index itself
(`TauCeti.Floer.SphericalCapClass.grading_eq`), and it is the grading `μ` of the capped orbit in
capped Hamiltonian Floer theory. Taking the nearest integer makes the recapping laws hold for every
`Φ`. -/
def grading (q : SphericalCapClass ω c γ) : ℤ :=
  round (conleyZehnderIndex h hc hcap hΦ hΦσ q)

/-- The defining equation of `TauCeti.Floer.SphericalCapClass.grading`. -/
theorem grading_def (q : SphericalCapClass ω c γ) :
    grading h hc hcap hΦ hΦσ q = round (conleyZehnderIndex h hc hcap hΦ hΦσ q) :=
  (rfl)

/-- At a nondegenerate orbit the grading of a cap class is its Conley–Zehnder index. -/
theorem grading_eq (hΦ₀ : ∀ v, Φ 0 v = v) (hΦ₁ : ∀ v, Φ 1 v = v → v = 0)
    (q : SphericalCapClass ω c γ) :
    (grading h hc hcap hΦ hΦσ q : ℝ) = conleyZehnderIndex h hc hcap hΦ hΦσ q := by
  obtain ⟨k, hk⟩ := exists_int_conleyZehnderIndex_eq h hc hcap hΦ hΦσ hΦ₀ hΦ₁ q
  rw [grading_def, hk, round_intCast]

/-- **Two cap classes differ by a class of the period group.** The gradings of two cap classes of
`γ` differ by minus the degree `2 c₁` of the class by which they differ. -/
theorem grading_sub_grading (q' q : SphericalCapClass ω c γ) :
    grading h hc hcap hΦ hΦσ q' - grading h hc hcap hΦ hΦσ q =
      -PeriodGroup.degree _ _ (q' -ᵥ q) := by
  have hq : conleyZehnderIndex h hc hcap hΦ hΦσ q' = conleyZehnderIndex h hc hcap hΦ hΦσ q +
      ((-PeriodGroup.degree _ _ (q' -ᵥ q) : ℤ) : ℝ) := by
    rw [Int.cast_neg, ← conleyZehnderIndex_sub_conleyZehnderIndex h hc hcap hΦ hΦσ q' q]
    ring
  rw [grading_def, grading_def, hq, round_add_intCast]
  ring

/-- Two cap classes of `γ` have the same grading exactly when the class of the period group by
which they differ has first Chern number zero. -/
theorem grading_eq_grading_iff {q' q : SphericalCapClass ω c γ} :
    grading h hc hcap hΦ hΦσ q' = grading h hc hcap hΦ hΦσ q ↔
      PeriodGroup.chern _ _ (q' -ᵥ q) = 0 := by
  rw [← sub_eq_zero, grading_sub_grading, neg_eq_zero, PeriodGroup.degree_apply, mul_eq_zero]
  simp

/-- **A cap class is determined by its action and its grading.** For a closed `C¹` two-form `α`
whose integral over every sphere is the value of `ω` on its Hurewicz class and any Hamiltonian
`Ham`, two cap classes of `γ` are equal exactly when they have the same capped action and the same
grading. -/
theorem eq_iff_action_eq_and_grading_eq [CompactSpace M] [I.Boundaryless]
    {α : RoughForm I M ℝ 2} {hα : IsSmoothForm I 1 α} {hdα : mextDeriv α = 0}
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hα hdα a) (Ham : ℝ → M → ℝ)
    {q' q : SphericalCapClass ω c γ} :
    q' = q ↔ action hα hdα hω Ham hcap q' = action hα hdα hω Ham hcap q ∧
      grading h hc hcap hΦ hΦσ q' = grading h hc hcap hΦ hΦσ q := by
  rw [grading_eq_grading_iff, eq_iff_action_eq_and_chern_vsub_eq_zero hω]

variable [PathConnectedSpace M]

/-- **The recapping law on cap classes.** Recapping a cap class by a class `B` of the period group
lowers its Conley–Zehnder index by the degree `2 c₁(B)` of `B`. -/
@[simp]
theorem conleyZehnderIndex_vadd (B : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    conleyZehnderIndex h hc hcap hΦ hΦσ (B +ᵥ q) =
      -(PeriodGroup.degree _ _ B : ℝ) + conleyZehnderIndex h hc hcap hΦ hΦσ q :=
  lift_vadd _ _ _ B q

/-- **The recapping law of the grading.** Recapping a cap class by a class `B` of the period group
lowers its grading by the degree `2 c₁(B)` of `B`, as it lowers the capped action by the area of
`B` (`TauCeti.Floer.SphericalCapClass.action_vadd`). -/
@[simp]
theorem grading_vadd (B : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    grading h hc hcap hΦ hΦσ (B +ᵥ q) = -PeriodGroup.degree _ _ B + grading h hc hcap hΦ hΦσ q := by
  rw [grading_def, grading_def, conleyZehnderIndex_vadd, ← Int.cast_neg, round_intCast_add]

end SphericalCapClass

end TauCeti.Floer
