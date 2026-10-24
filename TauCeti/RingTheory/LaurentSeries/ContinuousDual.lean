/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientDuality
public import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial

/-!
# The continuous residue dual of a Laurent-series field

Let `F = K((X))` have its valuation topology and give `K` the discrete topology. A `K`-linear
functional on `F` is continuous exactly when it vanishes on some lattice `U_a = X^a K[[X]]`.
Every such functional is uniquely `f ↦ Res(g f dX)` for a Laurent series `g`. Its coefficient
at exponent `n` is the value of the functional on `X^(-1-n)`.

The linear equivalence `TauCeti.LaurentSeries.residueDualEquiv` expresses this self-duality.
Throughout, `K` carries the discrete topology (`[DiscreteTopology K]`); no characteristic
assumption is needed. The lattice annihilator calculation also identifies the functionals
vanishing on `U_a` with the series in `U_(-a)`.

The construction uses the residue form and its lattice orthogonals from
`TauCeti.RingTheory.LaurentSeries.CoefficientDuality`, and Laurent-polynomial density to
recover a continuous functional from its values on monomials.
-/

public section

open HahnSeries Filter Topology
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K] [TopologicalSpace K] [DiscreteTopology K]

/-- A linear functional to the discrete coefficient field is continuous exactly when it
vanishes on some Laurent lattice. -/
theorem continuous_linearMap_iff_exists_lattice_le_ker (ℓ : K⸨X⸩ →ₗ[K] K) :
    Continuous ℓ ↔ ∃ a : ℤ, lattice K K a ≤ LinearMap.ker ℓ := by
  constructor
  · intro hℓ
    have hzero : ∀ᶠ f in 𝓝 (0 : K⸨X⸩), ℓ f = 0 := by
      exact hℓ.continuousAt.preimage_mem_nhds
        ((isOpen_discrete {0}).mem_nhds (by simp))
    obtain ⟨a, -, ha⟩ := hasBasis_nhds_zero_lattice.eventually_iff.mp hzero
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    apply continuous_of_continuousAt_zero ℓ.toAddMonoidHom
    simp only [ContinuousAt, map_zero, nhds_discrete K, tendsto_pure]
    exact hasBasis_nhds_zero_lattice.eventually_iff.mpr ⟨a, trivial, ha⟩

/-- Residue pairing with any fixed Laurent series is a continuous functional to discrete `K`. -/
theorem continuous_residueForm (g : K⸨X⸩) : Continuous (residueForm K g) := by
  apply (continuous_linearMap_iff_exists_lattice_le_ker _).mpr
  refine ⟨-g.order, fun f hf ↦ ?_⟩
  exact residueForm_eq_zero_of_mem_lattice
    (mem_lattice_iff.mpr fun _ hn ↦ coeff_eq_zero_of_lt_order hn) hf (by omega)

/-- The continuous functional `f ↦ Res(g f dX)`. -/
noncomputable def residueDual (g : K⸨X⸩) : K⸨X⸩ →L[K] K where
  toLinearMap := residueForm K g
  cont := continuous_residueForm g

-- Keep general evaluation explicit so that simp retains the monomial rule below.
theorem residueDual_apply (g f : K⸨X⸩) : residueDual g f = (g * f).coeff (-1) :=
  residueForm_apply g f

/-- Pairing with `X^n` reads the coefficient at `-1-n` of the representing series. -/
@[simp]
theorem residueDual_single (g : K⸨X⸩) (n : ℤ) :
    residueDual g (single n 1) = g.coeff (-1 - n) := by
  simp only [residueDual_apply, coeff_mul_single, mul_one]

/-- The coefficient at `n` is recovered by residue pairing with `X^(-1-n)`. -/
theorem coeff_eq_residueDual_single (g : K⸨X⸩) (n : ℤ) :
    g.coeff n = residueDual g (single (-1 - n) 1) := by
  rw [residueDual_single, sub_sub_cancel]

/-- A Laurent series is determined by its continuous residue functional. -/
theorem residueDual_injective : Function.Injective (residueDual (K := K)) := by
  intro g h heq
  ext n
  rw [coeff_eq_residueDual_single, coeff_eq_residueDual_single, heq]

/-- Every continuous functional is residue pairing with a unique Laurent series. -/
theorem existsUnique_residueDual (ℓ : K⸨X⸩ →L[K] K) :
    ∃! g : K⸨X⸩, residueDual g = ℓ := by
  obtain ⟨a, ha⟩ := (continuous_linearMap_iff_exists_lattice_le_ker ℓ.toLinearMap).mp ℓ.continuous
  have hbdd : BddBelow (Function.support fun n : ℤ ↦ ℓ (single (-1 - n) 1)) := by
    refine ⟨-a, fun n hn ↦ ?_⟩
    by_contra! h
    exact hn (ha (single_mem_lattice (by omega) 1))
  let g : K⸨X⸩ := ofSuppBddBelow (fun n : ℤ ↦ ℓ (single (-1 - n) 1)) hbdd
  have hg : residueDual g = ℓ := by
    apply continuousLinearMap_ext_single
    intro n
    simp only [residueDual_single, g, coeff_ofSuppBddBelow, sub_sub_cancel]
  exact ⟨g, hg, fun f hf ↦ residueDual_injective (hf.trans hg.symm)⟩

/-- Residue pairing identifies Laurent series with their continuous `K`-linear dual to the
discrete coefficient field. -/
noncomputable def residueDualEquiv : K⸨X⸩ ≃ₗ[K] (K⸨X⸩ →L[K] K) :=
  LinearEquiv.ofBijective
    { toFun := residueDual
      map_add' := fun g h ↦ by ext f; simp [residueDual_apply, add_mul]
      map_smul' := fun c g ↦ by ext f; simp [residueDual_apply, smul_mul_assoc] }
    ⟨residueDual_injective, fun ℓ ↦ (existsUnique_residueDual ℓ).exists⟩

-- Keeping the equivalence bundled lets simp cancel it against its inverse.
theorem residueDualEquiv_apply (g : K⸨X⸩) : residueDualEquiv g = residueDual g := (rfl)

/-- The coefficient at `n` of the series representing `ℓ` is `ℓ (X^(-1-n))`. -/
@[simp]
theorem coeff_residueDualEquiv_symm (ℓ : K⸨X⸩ →L[K] K) (n : ℤ) :
    (residueDualEquiv.symm ℓ).coeff n = ℓ (single (-1 - n) 1) := by
  rw [coeff_eq_residueDual_single, ← residueDualEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The functional represented by `g` vanishes on `U_a` exactly when `g` belongs to `U_(-a)`. -/
theorem lattice_le_ker_residueDual_iff (g : K⸨X⸩) (a : ℤ) :
    lattice K K a ≤ LinearMap.ker (residueDual g).toLinearMap ↔ g ∈ lattice K K (-a) := by
  rw [← residueForm_orthogonal_lattice, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor <;> intro h f hf
  · rw [residueForm_isSymm.eq]
    exact h hf
  · exact (residueForm_isSymm.eq _ _).trans (h f hf)

end TauCeti.LaurentSeries
