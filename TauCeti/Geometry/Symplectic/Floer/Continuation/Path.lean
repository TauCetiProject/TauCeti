/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex

/-!
# The path of Floer data between two sets of data

Two sets of Floer data on a domain `Z`, such as the cylinder `ℝ × ℝ` or its product with a
parameter space, given by almost complex structures `J z y` and `J' z y` and Hamiltonians `K z y`
and `K' z y` at the domain point `z` and the target point `y`, are joined by a path of data with
parameter `μ`, which is the first set of data at `μ = 0` and the second at `μ = 1`. Its almost
complex structures `TauCeti.Floer.pathAlmostComplex` run, for each `(z, y)`, along the continuation
homotopy `TauCeti.Floer.continuationAlmostComplex` from `J z y` to `J' z y`, with the parameter `μ`
as its homotopy coordinate `s` (at time `0`); so they are tame
(`TauCeti.Floer.tames_pathAlmostComplex`), their Cayley coordinates relative to a fixed compatible
structure run along the segment between those of `J z y` and `J' z y`
(`TauCeti.Floer.cayley_pathAlmostComplex`), and they are compatible wherever both `J` and `J'` are.
Its Hamiltonians `TauCeti.Floer.pathHamiltonian` run along the segment `K + μ (K' - K)`, the linear
homotopy `TauCeti.Floer.linearHomotopy` with profile `id`.

The path is the first set of data at `μ = 0` and the second at `μ = 1`
(`TauCeti.Floer.pathAlmostComplex_zero`, `TauCeti.Floer.pathAlmostComplex_one`,
`TauCeti.Floer.pathHamiltonian_zero`, `TauCeti.Floer.pathHamiltonian_one`); its almost complex
structures are already `J` for `μ ≤ 0` and `J'` for `μ ≥ 1`
(`TauCeti.Floer.pathAlmostComplex_of_nonpos`, `TauCeti.Floer.pathAlmostComplex_of_one_le`). It is
their common value where the two sets of data agree (`TauCeti.Floer.pathAlmostComplex_of_eq`,
`TauCeti.Floer.pathHamiltonian_of_eq`), is
compatible where both almost complex structures are
(`TauCeti.Floer.compatible_pathAlmostComplex`), and is `Cⁿ` jointly in the parameter, the domain
point and the target point where the two sets of data are
(`TauCeti.Floer.contDiffAt_pathAlmostComplex`, `TauCeti.Floer.contDiffAt_pathHamiltonian`).
Deforming the data along this path is how the Fredholm index of a linearized Floer operator is shown
not to depend on the data away from the ends.

## Main definitions

* `TauCeti.Floer.pathAlmostComplex`: the path of almost complex structures from `J` to `J'`.
* `TauCeti.Floer.pathHamiltonian`: the segment of Hamiltonians from `K` to `K'`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the spaces of tame and compatible structures.
-/

public noncomputable section

open Function Real

namespace TauCeti.Floer

section AlmostComplex

variable {Z V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The path of almost complex structures from `J` to `J'`: at `(μ, z)` and `y` it is the
continuation homotopy, relative to `J₀`, from `J z y` to `J' z y` at the homotopy coordinate
`s = μ` (and time `0`). It is `J` for `μ ≤ 0` and `J'` for `μ ≥ 1`. -/
def pathAlmostComplex (h₀ : ω.Compatible J₀) {J J' : Z → V → AlmostComplexStructure V}
    (hJ : ∀ z y, ω.Tames (J z y)) (hJ' : ∀ z y, ω.Tames (J' z y)) (p : ℝ × Z) (y : V) :
    AlmostComplexStructure V :=
  continuationAlmostComplex h₀ (fun _ q ↦ J q.1 q.2) (fun _ q ↦ J' q.1 q.2)
    (fun _ q ↦ hJ q.1 q.2) (fun _ q ↦ hJ' q.1 q.2) (p.1, 0) (p.2, y)

variable {J J' : Z → V → AlmostComplexStructure V} {hJt : ∀ z y, ω.Tames (J z y)}
  {hJ't : ∀ z y, ω.Tames (J' z y)}

/-- The path of almost complex structures is `ω`-tame. -/
theorem tames_pathAlmostComplex (h₀ : ω.Compatible J₀) (p : ℝ × Z) (y : V) :
    ω.Tames (pathAlmostComplex h₀ hJt hJ't p y) := by
  rw [pathAlmostComplex]
  exact tames_continuationAlmostComplex h₀ _ _

/-- The Cayley transform of the path of almost complex structures, relative to `J₀`, at `(μ, z)`
and `y` is `(1 - smoothTransition μ) • cayley (J z y) + smoothTransition μ • cayley (J' z y)`. This
characterizes the structure, since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_pathAlmostComplex (h₀ : ω.Compatible J₀) (μ : ℝ) (z : Z) (y : V) :
    J₀.cayley (pathAlmostComplex h₀ hJt hJ't (μ, z) y) =
      (1 - smoothTransition μ) • J₀.cayley (J z y) + smoothTransition μ • J₀.cayley (J' z y) := by
  rw [pathAlmostComplex]
  exact cayley_continuationAlmostComplex h₀ _ _

/-- The path of almost complex structures is `J` for `μ ≤ 0`. -/
theorem pathAlmostComplex_of_nonpos (h₀ : ω.Compatible J₀) {μ : ℝ} (hμ : μ ≤ 0) (z : Z)
    (y : V) : pathAlmostComplex h₀ hJt hJ't (μ, z) y = J z y :=
  h₀.eq_of_cayley_eq (tames_pathAlmostComplex h₀ _ y) (hJt z y) (by
    simp [smoothTransition.zero_of_nonpos hμ])

/-- The path of almost complex structures is `J'` for `μ ≥ 1`. -/
theorem pathAlmostComplex_of_one_le (h₀ : ω.Compatible J₀) {μ : ℝ} (hμ : 1 ≤ μ) (z : Z)
    (y : V) : pathAlmostComplex h₀ hJt hJ't (μ, z) y = J' z y :=
  h₀.eq_of_cayley_eq (tames_pathAlmostComplex h₀ _ y) (hJ't z y) (by
    simp [smoothTransition.one_of_one_le hμ])

/-- The path of almost complex structures is `J` at `μ = 0`. -/
@[simp]
theorem pathAlmostComplex_zero (h₀ : ω.Compatible J₀) (z : Z) (y : V) :
    pathAlmostComplex h₀ hJt hJ't (0, z) y = J z y :=
  pathAlmostComplex_of_nonpos h₀ le_rfl z y

/-- The path of almost complex structures is `J'` at `μ = 1`. -/
@[simp]
theorem pathAlmostComplex_one (h₀ : ω.Compatible J₀) (z : Z) (y : V) :
    pathAlmostComplex h₀ hJt hJ't (1, z) y = J' z y :=
  pathAlmostComplex_of_one_le h₀ le_rfl z y

/-- Where `J` and `J'` agree, the path of almost complex structures is their common value, at
every parameter. -/
theorem pathAlmostComplex_of_eq (h₀ : ω.Compatible J₀) (μ : ℝ) {z : Z} {y : V}
    (h : J z y = J' z y) : pathAlmostComplex h₀ hJt hJ't (μ, z) y = J z y := by
  rw [pathAlmostComplex]
  exact continuationAlmostComplex_of_eq h₀ h

/-- At each parameter, the path of almost complex structures at `z` depends only on `J z` and
`J' z`. -/
theorem pathAlmostComplex_congr (h₀ : ω.Compatible J₀) (μ : ℝ) {z z' : Z}
    (h : J z = J z') (h' : J' z = J' z') :
    pathAlmostComplex h₀ hJt hJ't (μ, z) = pathAlmostComplex h₀ hJt hJ't (μ, z') := by
  funext y
  exact h₀.eq_of_cayley_eq (tames_pathAlmostComplex h₀ _ y) (tames_pathAlmostComplex h₀ _ y)
    (by rw [cayley_pathAlmostComplex, cayley_pathAlmostComplex, h, h'])

/-- The path of almost complex structures is `ω`-compatible at `(p, y)` when `J` and `J'` are
`ω`-compatible at `(p.2, y)`. -/
theorem compatible_pathAlmostComplex (h₀ : ω.Compatible J₀) {p : ℝ × Z} {y : V}
    (hJ : ω.Compatible (J p.2 y)) (hJ' : ω.Compatible (J' p.2 y)) :
    ω.Compatible (pathAlmostComplex h₀ hJt hJ't p y) := by
  rw [pathAlmostComplex]
  exact compatible_continuationAlmostComplex h₀ hJ hJ'

end AlmostComplex

section Hamiltonian

variable {Z V : Type*}

/-- The segment of Hamiltonians from `K` to `K'`, with parameter `μ`: the linear homotopy with
profile `id` from `K` to `K'`, viewed as time-independent Hamiltonians on `Z × V`. -/
def pathHamiltonian (K K' : Z → V → ℝ) (p : ℝ × Z) (y : V) : ℝ :=
  linearHomotopy id (fun _ q ↦ K q.1 q.2) (fun _ q ↦ K' q.1 q.2) (p.1, 0) (p.2, y)

/-- The segment of Hamiltonians at the parameter `μ` is `K + μ (K' - K)`. -/
@[simp]
theorem pathHamiltonian_apply (K K' : Z → V → ℝ) (μ : ℝ) (z : Z) (y : V) :
    pathHamiltonian K K' (μ, z) y = K z y + μ * (K' z y - K z y) := by
  rw [pathHamiltonian, linearHomotopy_def, id]

/-- The segment of Hamiltonians is `K` at `μ = 0`. -/
@[simp]
theorem pathHamiltonian_zero (K K' : Z → V → ℝ) (z : Z) :
    pathHamiltonian K K' (0, z) = K z := by
  funext y
  rw [pathHamiltonian_apply, zero_mul, add_zero]

/-- The segment of Hamiltonians is `K'` at `μ = 1`. -/
@[simp]
theorem pathHamiltonian_one (K K' : Z → V → ℝ) (z : Z) :
    pathHamiltonian K K' (1, z) = K' z := by
  funext y
  rw [pathHamiltonian_apply, one_mul, add_sub_cancel]

/-- At a point `z` where the two Hamiltonians agree, every member of the segment of Hamiltonians
is their common value. -/
theorem pathHamiltonian_of_eq {K K' : Z → V → ℝ} (μ : ℝ) {z : Z} (h : K z = K' z) :
    pathHamiltonian K K' (μ, z) = K z := by
  funext y
  rw [pathHamiltonian_apply, h, sub_self, mul_zero, add_zero]

end Hamiltonian

section Smooth

variable {Z V : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The segment of Hamiltonians is `Cⁿ` at `((μ, z), y)` when its endpoints are `Cⁿ` at `(z, y)`,
jointly in the domain and target point. -/
theorem contDiffAt_pathHamiltonian {n : ℕ∞} {K K' : Z → V → ℝ} {p : ℝ × Z} {y : V}
    (hK : ContDiffAt ℝ n (uncurry K) (p.2, y)) (hK' : ContDiffAt ℝ n (uncurry K') (p.2, y)) :
    ContDiffAt ℝ n (uncurry (pathHamiltonian K K')) (p, y) := by
  have h := contDiffAt_uncurry_linearHomotopy (n := n) (β := id)
    (H₀ := fun (_ : ℝ) (q : Z × V) ↦ K q.1 q.2)
    (H₁ := fun (_ : ℝ) (q : Z × V) ↦ K' q.1 q.2) (p := ((p.1, 0), (p.2, y))) contDiffAt_id
    (hK.comp (0, (p.2, y)) contDiffAt_snd) (hK'.comp (0, (p.2, y)) contDiffAt_snd)
  unfold pathHamiltonian
  exact h.comp (p, y) ((contDiff_fst.fst.prodMk contDiff_const).prodMk
    (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt

/-- The segment of Hamiltonians is `Cⁿ` when its endpoints are. -/
theorem contDiff_pathHamiltonian {n : ℕ∞} {K K' : Z → V → ℝ} (hK : ContDiff ℝ n (uncurry K))
    (hK' : ContDiff ℝ n (uncurry K')) : ContDiff ℝ n (uncurry (pathHamiltonian K K')) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_pathHamiltonian hK.contDiffAt hK'.contDiffAt

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J J' : Z → V → AlmostComplexStructure V}

/-- The path of almost complex structures is `Cⁿ` at `((μ, z), y)` when its endpoints are `Cⁿ` at
`(z, y)`, jointly in the domain and target point. -/
theorem contDiffAt_pathAlmostComplex {n : ℕ∞} (h₀ : ω.Compatible J₀)
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y)) {p : ℝ × Z} {y : V}
    (hJ : ContDiffAt ℝ n (fun q : Z × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap)
      (p.2, y))
    (hJ' : ContDiffAt ℝ n (fun q : Z × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap)
      (p.2, y)) :
    ContDiffAt ℝ n (fun q : (ℝ × Z) × V ↦
      (pathAlmostComplex h₀ hJt hJ't q.1 q.2).toLinearMap.toContinuousLinearMap) (p, y) := by
  have h₁ : ContDiffAt ℝ n (fun r : ℝ × (Z × V) ↦
      (J r.2.1 r.2.2).toLinearMap.toContinuousLinearMap) (0, (p.2, y)) :=
    hJ.comp (f := Prod.snd) (0, (p.2, y)) contDiffAt_snd
  have h₂ : ContDiffAt ℝ n (fun r : ℝ × (Z × V) ↦
      (J' r.2.1 r.2.2).toLinearMap.toContinuousLinearMap) (0, (p.2, y)) :=
    hJ'.comp (f := Prod.snd) (0, (p.2, y)) contDiffAt_snd
  have h := contDiffAt_continuationAlmostComplex (n := n) h₀ (hJ₁ := fun _ q ↦ hJt q.1 q.2)
    (hJ₂ := fun _ q ↦ hJ't q.1 q.2) (p := ((p.1, 0), (p.2, y))) h₁ h₂
  have hπ : ContDiffAt ℝ n (fun q : (ℝ × Z) × V ↦ ((q.1.1, (0 : ℝ)), (q.1.2, q.2))) (p, y) :=
    ((contDiff_fst.fst.prodMk contDiff_const).prodMk
      (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  -- After unfolding, the path is the continuation homotopy at `((μ, 0), (z, y))`, so the claim is
  -- `h` composed with `hπ`; the ascription elaborates the composition before matching the goal.
  unfold pathAlmostComplex
  exact (h.comp (p, y) hπ :)

/-- The path of almost complex structures is `Cⁿ` when its endpoints are. -/
theorem contDiff_pathAlmostComplex {n : ℕ∞} (h₀ : ω.Compatible J₀)
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hJ : ContDiff ℝ n fun q : Z × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJ' : ContDiff ℝ n fun q : Z × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) :
    ContDiff ℝ n fun q : (ℝ × Z) × V ↦
      (pathAlmostComplex h₀ hJt hJ't q.1 q.2).toLinearMap.toContinuousLinearMap :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    contDiffAt_pathAlmostComplex h₀ hJt hJ't hJ.contDiffAt hJ'.contDiffAt

end Smooth

end TauCeti.Floer
