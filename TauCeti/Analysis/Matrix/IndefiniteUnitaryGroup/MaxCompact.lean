/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Analysis.HeisenbergModel.Fock.Basic
public import TauCeti.LinearAlgebra.Matrix.Diagonal.Commutant
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Polar
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
import TauCeti.Topology.Algebra.Matrix.UnitaryGroup.Basic
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The maximal compact subgroup of `U(ε)` and exponentials

For signs `ε : ι → ℤˣ`, let `G = U(ε)` be the unitary group of the hermitian form of `diag(ε)`
(`TauCeti.Fock.unitaryGroup ε`, which is `U(p, q)` for `p` signs `+1` and `q` signs `-1`), and
`K = G ∩ U(n)` its maximal compact subgroup `U(p) × U(q)` (`TauCeti.Fock.maxCompact ε`). This file
proves:

* an element of `G` lies in `K` exactly when it is block diagonal for the signs, that is, commutes
  with `diag(ε)` (`TauCeti.Fock.mem_maxCompact_iff_commute`,
  `TauCeti.Fock.mem_maxCompact_iff_blockDiagPart_eq`); the block diagonal part of a matrix `x` is
  `(x + diag(ε) x diag(ε)) / 2` (`Matrix.blockDiagPart_eq_inv_two_smul`);
* `K` is compact (`TauCeti.Fock.isCompact_maxCompact`);
* every `k ∈ K` is `exp X` for a skew-hermitian `X` that commutes with `diag(ε)`, and every
  `g ∈ G` is `exp X · exp Y` with `X` and `Y` in the Lie algebra `{X | X* diag(ε) + diag(ε) X = 0}`
  of `G` (`TauCeti.Fock.exists_exp_eq_of_mem_maxCompact`,
  `TauCeti.Fock.exists_exp_mul_exp_eq_of_mem_unitaryGroup`). The logarithm of `k` is
  `log k` for the continuous functional calculus: the spectrum of `k` is a finite subset of the
  unit circle, on which `log` is continuous and `conj ∘ log = -log`, and `log k` commutes with
  everything that commutes with `k` and `k*`. The second statement combines this with the polar
  decomposition `g = k · exp Y` (`Matrix.unitaryGroupOf.existsUnique_unitary_mul_exp`);
* the block diagonal part of every `g ∈ G` is invertible
  (`TauCeti.Fock.det_blockDiagPart_ne_zero`): if it kills `v`, then `g` maps the part `v_s` of `v`
  on the indices of sign `s` to a vector with no coordinates of sign `s`, and comparing the values
  of the form at `v_s` and `g v_s` shows `v_s = 0`.

## Main definitions

* `TauCeti.Fock.maxCompact ε`: the maximal compact subgroup `U(ε) ∩ U(n)`.

## Main results

* `TauCeti.Fock.mem_maxCompact_iff_commute`, `TauCeti.Fock.mem_maxCompact_iff_blockDiagPart_eq`:
  the elements of `K` are the block diagonal elements of `G`.
* `TauCeti.Fock.isCompact_maxCompact`: `K` is compact.
* `TauCeti.Fock.exists_exp_eq_of_mem_maxCompact`,
  `TauCeti.Fock.exists_exp_mul_exp_eq_of_mem_unitaryGroup`: exponentials in `K` and `G`.
* `TauCeti.Fock.det_blockDiagPart_ne_zero`: the block diagonal part of an element of `G` is
  invertible.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Chapter VI.
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the statements follow `New.maxCompactU`, `New.mem_maxCompactU` and
  `New.blockDiagPart_eq` in `src/Lib/DiscreteSeries/Holomorphic/MaximalCompactMinors.lean`, and
  `New.exists_expU_eq_maxCompactU` and `New.exists_eq_expU_mul_expU` in
  `src/Lib/DiscreteSeries/Holomorphic/HighestVectorExtension.lean`.
-/

public section

open Matrix NormedSpace

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ)

/-- The **maximal compact subgroup** `K = U(ε) ∩ U(n)` of the unitary group `U(ε)` of the
hermitian form of `diag(ε)`: the block diagonal elements `U(p) × U(q)` of `U(ε)`
(`TauCeti.Fock.mem_maxCompact_iff_commute`). -/
def maxCompact : Subgroup (GL ι ℂ) :=
  unitaryGroup ε ⊓ unitarySubgroup (GL ι ℂ)

variable {ε}

theorem mem_maxCompact_iff {g : GL ι ℂ} :
    g ∈ maxCompact ε ↔ g ∈ unitaryGroup ε ∧ g ∈ unitarySubgroup (GL ι ℂ) :=
  Iff.rfl

theorem maxCompact_le_unitaryGroup : maxCompact ε ≤ unitaryGroup ε :=
  inf_le_left

/-- **The elements of `K` are the block diagonal elements of `U(ε)`**: an element of `U(ε)` is
unitary exactly when it commutes with `diag(ε)`. -/
theorem mem_maxCompact_iff_commute {g : GL ι ℂ} :
    g ∈ maxCompact ε ↔ g ∈ unitaryGroup ε ∧ Commute (signMatrix ε) (g : Matrix ι ι ℂ) :=
  and_congr_right (mem_unitarySubgroup_GL_iff_commute isUnit_signMatrix)

/-- The elements of `K` are the elements of `U(ε)` that are their own block diagonal part. -/
theorem mem_maxCompact_iff_blockDiagPart_eq {g : GL ι ℂ} :
    g ∈ maxCompact ε ↔
      g ∈ unitaryGroup ε ∧ (g : Matrix ι ι ℂ).blockDiagPart ε = (g : Matrix ι ι ℂ) := by
  have hinj : Function.Injective fun s : ℤˣ ↦ ((s : ℤ) : ℂ) :=
    Int.cast_injective.comp Units.val_injective
  have hrel : (g : Matrix ι ι ℂ).blockDiagPart (fun a ↦ ((ε a : ℤ) : ℂ)) =
      (g : Matrix ι ι ℂ).blockDiagPart ε :=
    blockDiagPart_comp hinj _ ε
  rw [mem_maxCompact_iff_commute, signMatrix_eq_diagonal, commute_diagonal_iff_blockDiagPart_eq,
    hrel]

/-- The block diagonal part of an element of `K` is itself. -/
theorem blockDiagPart_eq_of_mem_maxCompact {k : GL ι ℂ} (hk : k ∈ maxCompact ε) :
    (k : Matrix ι ι ℂ).blockDiagPart ε = k :=
  (mem_maxCompact_iff_blockDiagPart_eq.1 hk).2

/-- **`K` is compact**: it is a closed subset of the compact unitary group. -/
theorem isCompact_maxCompact : IsCompact (maxCompact ε : Set (GL ι ℂ)) := by
  rw [maxCompact, Subgroup.coe_inf]
  exact GeneralLinearGroup.isCompact_unitarySubgroup.inter_left
    (isClosed_unitaryGroupOf _)

instance : CompactSpace (maxCompact ε) :=
  isCompact_iff_compactSpace.1 isCompact_maxCompact

open scoped Matrix.Norms.L2Operator in
/-- **Logarithms in `K`.** Every `k ∈ K` is `exp X` for a skew-hermitian `X` commuting with
`diag(ε)`, a block diagonal element of the Lie algebra of `U(ε)`. -/
theorem exists_exp_eq_of_mem_maxCompact {k : GL ι ℂ} (hk : k ∈ maxCompact ε) :
    ∃ X : Matrix ι ι ℂ, star X = -X ∧ Commute (signMatrix ε) X ∧ exp X = k := by
  have hkJ : Commute (k : Matrix ι ι ℂ) (signMatrix ε) := (mem_maxCompact_iff_commute.1 hk).2.symm
  have hu : (k : Matrix ι ι ℂ) ∈ unitary (Matrix ι ι ℂ) :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 hk.2
  have hspec : ∀ z ∈ spectrum ℂ (k : Matrix ι ι ℂ), ‖z‖ = 1 :=
    spectrum.norm_eq_one_of_unitary hu
  have hcont (f : ℂ → ℂ) : ContinuousOn f (spectrum ℂ (k : Matrix ι ι ℂ)) :=
    (Matrix.finite_spectrum _).continuousOn f
  refine ⟨cfc Complex.log (k : Matrix ι ι ℂ), ?_, ?_, ?_⟩
  · -- On the unit circle, `log z` is purely imaginary.
    rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz ↦ Complex.ext ?_ ?_ <;>
      simp [Complex.log_re, hspec z hz]
  · have hstar : Commute (star (k : Matrix ι ι ℂ)) (signMatrix ε) := by
      simpa [star_eq_conjTranspose] using hkJ.star_star
    exact (hkJ.cfc hstar Complex.log).symm
  · rw [← CFC.complex_exp_eq_normedSpace_exp,
      ← cfc_comp Complex.exp Complex.log _ (hg := Complex.continuous_exp.continuousOn)
        (hf := hcont _)]
    conv_rhs => rw [← cfc_id' ℂ (k : Matrix ι ι ℂ)]
    refine cfc_congr fun z hz ↦ Complex.exp_log ?_
    rw [← norm_ne_zero_iff, hspec z hz]
    exact one_ne_zero

/-- **Exponentials in `U(ε)`.** Every `g ∈ U(ε)` is `exp X · exp Y` with `X` and `Y` in the Lie
algebra `{X | X* diag(ε) + diag(ε) X = 0}` of `U(ε)`. -/
theorem exists_exp_mul_exp_eq_of_mem_unitaryGroup {g : GL ι ℂ} (hg : g ∈ unitaryGroup ε) :
    ∃ X Y : Matrix ι ι ℂ, star X * signMatrix ε + signMatrix ε * X = 0 ∧
      star Y * signMatrix ε + signMatrix ε * Y = 0 ∧ exp X * exp Y = (g : Matrix ι ι ℂ) := by
  obtain ⟨⟨⟨u, hu⟩, Y, hY⟩, hgY, -⟩ :=
    unitaryGroupOf.existsUnique_unitary_mul_exp signMatrix_mul_signMatrix ⟨g, hg⟩
  have hgY' : (g : Matrix ι ι ℂ) = (u : Matrix ι ι ℂ) * exp (Y : Matrix ι ι ℂ) := by
    simpa using hgY
  have hk : Unitary.toUnits u ∈ maxCompact ε :=
    ⟨hu, mem_unitarySubgroup_GL_iff_mem_unitaryGroup.2 (by simp)⟩
  obtain ⟨X, hXs, hXJ, hX⟩ := exists_exp_eq_of_mem_maxCompact hk
  refine ⟨X, Y, ?_, ?_, ?_⟩
  · rw [hXs, neg_mul, hXJ.eq, neg_add_cancel]
  · rw [Y.property.star_eq, add_comm, hY]
  · rw [hX, hgY', Unitary.val_toUnits_apply]

/-- **The block diagonal part of an element of `U(ε)` is invertible.** -/
theorem det_blockDiagPart_ne_zero {g : GL ι ℂ} (hg : g ∈ unitaryGroup ε) :
    ((g : Matrix ι ι ℂ).blockDiagPart ε).det ≠ 0 := by
  rw [Ne, ← exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hgv⟩
  refine hv (funext fun a ↦ ?_)
  -- The part `w` of `v` on the indices of the sign `s` of `a` is mapped by `g` to a vector with
  -- no coordinates of sign `s`.
  set s := ε a
  set w : ι → ℂ := fun b ↦ if ε b = s then v b else 0
  have hgw (c : ι) (hc : ε c = s) : ((g : Matrix ι ι ℂ) *ᵥ w) c = 0 := by
    have hc' := congr_fun hgv c
    rw [Pi.zero_apply] at hc'
    rw [← hc']
    simp only [mulVec, dotProduct, blockDiagPart_apply, hc, w, mul_ite, mul_zero, ite_mul,
      zero_mul, eq_comm (a := s)]
  -- The values of the form at `w` and `g w`, multiplied by the sign `s`.
  have hform := (mem_unitaryGroupOf_iff_forall_dotProduct.1 hg) w w
  rw [star_dotProduct_signMatrix_mulVec, star_dotProduct_signMatrix_mulVec] at hform
  have hsign (c : ι) : ((s : ℤ) : ℂ) * ((ε c : ℤ) : ℂ) = if ε c = s then 1 else -1 := by
    rcases Int.units_eq_one_or s with h | h <;> rcases Int.units_eq_one_or (ε c) with h' | h' <;>
      simp [h, h']
  have hre (x : ι → ℂ) :
      (((s : ℤ) : ℂ) * ∑ c, ((ε c : ℤ) : ℂ) * (starRingEnd ℂ (x c) * x c)).re =
        ∑ c, if ε c = s then Complex.normSq (x c) else -Complex.normSq (x c) := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [← mul_assoc, hsign, ← Complex.normSq_eq_conj_mul_self]
    split_ifs <;> simp
  have hle : Complex.normSq (v a) ≤ 0 := by
    have h₁ := hre ((g : Matrix ι ι ℂ) *ᵥ w)
    have h₂ := hre w
    rw [hform] at h₁
    rw [h₁] at h₂
    have hnonpos : ∑ c, (if ε c = s then Complex.normSq (((g : Matrix ι ι ℂ) *ᵥ w) c)
        else -Complex.normSq (((g : Matrix ι ι ℂ) *ᵥ w) c)) ≤ 0 :=
      Finset.sum_nonpos fun c _ ↦ by
        split_ifs with hc
        · rw [hgw c hc, map_zero]
        · exact neg_nonpos.2 (Complex.normSq_nonneg _)
    have hge : Complex.normSq (v a) ≤
        ∑ c, if ε c = s then Complex.normSq (w c) else -Complex.normSq (w c) := by
      refine (le_of_eq (by simp [w, s])).trans
        (Finset.single_le_sum (f := fun c ↦ if ε c = s then Complex.normSq (w c)
          else -Complex.normSq (w c)) (fun c _ ↦ ?_) (Finset.mem_univ a))
      split_ifs with hc
      · exact Complex.normSq_nonneg _
      · simp [w, hc]
    linarith
  exact Complex.normSq_eq_zero.1 (le_antisymm hle (Complex.normSq_nonneg _))

end TauCeti.Fock
