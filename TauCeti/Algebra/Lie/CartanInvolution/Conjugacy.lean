/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# Conjugacy of Cartan involutions

Any two Cartan involutions `θ` and `θ'` of a real Lie algebra `L` are conjugate by an inner
automorphism of the form `exp (ad Z)` with `Z ∈ cartanP θ`.

Following Knapp (Chapter VI, Theorem 6.16), the automorphism `ω = θ ∘ θ'` is self-adjoint with
respect to the positive-definite inner product `B_θ(x, y) = -κ(x, θ y)`, so `P = ω²` is symmetric
and strictly positive. In an orthonormal eigenbasis `(b_i)` of `P` with positive eigenvalues `μ_i`,
the functional-calculus operators `P^s` (`b_i ↦ μ_i^s • b_i`) form a one-parameter family of Lie
algebra automorphisms, and `log P` (`b_i ↦ log μ_i • b_i`) is a Lie derivation of `L`. Because `L`
is Killing, `log P = ad Z₀` for some `Z₀ ∈ L`; the anti-commutation `log P ∘ θ = -θ ∘ log P`
together with `center ℝ L = ⊥` forces `Z₀ ∈ cartanP θ`. Setting `φ = P^{-1/4}` and
`Z = (-1/4) • Z₀ ∈ cartanP θ`, the conjugated Cartan involution `φ ∘ θ ∘ φ⁻¹` commutes with `θ'`,
hence equals `θ'` since commuting Cartan involutions coincide.

To avoid norm-instance diamonds between the `B_θ`-inner product used inside the spectral proof and
an arbitrary ambient norm on `L`, the spectral construction is separated into a purely algebraic
eigenbasis theorem (`TauCeti.IsCartanInvolution.exists_conj_basis`) that requires no norm on `L`.
Transported along any linear equivalence `e : L ≃ₗ[ℝ] E` into a finite-dimensional real normed
space, `exp (e.conj (ad Z))` agrees with `e.conj φ` on the eigenbasis and therefore everywhere
(`TauCeti.IsCartanInvolution.exists_exp_ad_conj_of_linearEquiv`).

## Main results

* `TauCeti.maximal_abelian_cartanP_map_iff`: an intertwining Lie equivalence preserves maximal
  abelian subspaces of `cartanP`.
* `TauCeti.IsCartanInvolution.eq_of_commute`: two commuting Cartan involutions are equal.
* `TauCeti.IsCartanInvolution.exists_conj_basis`: purely algebraic conjugacy exhibiting `Z ∈ 𝔭_θ`,
  an intertwining automorphism `φ`, and an eigenbasis on which `ad Z` acts by `c_i` and `φ` acts
  by `Real.exp (c_i)`.
* `TauCeti.IsCartanInvolution.exists_lieEquiv_conj`: any two Cartan involutions are conjugate by a
  Lie algebra automorphism.
* `TauCeti.IsCartanInvolution.exists_exp_ad_conj_of_linearEquiv`: transported into any
  finite-dimensional real normed space, any two Cartan involutions are conjugate by `exp (ad Z)`
  for some `Z ∈ cartanP θ`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16 and Corollary 6.19.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, §7, Theorem 7.2.
-/

public section

open LieAlgebra

namespace TauCeti

/-! ### Transport of maximal abelian subspaces of `𝔭` -/

section Intertwining

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- An intertwining Lie equivalence maps a subspace of `L` to a maximal abelian subspace of
`cartanP θ'` if and only if it is a maximal abelian subspace of `cartanP θ`. -/
theorem maximal_abelian_cartanP_map_iff (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) (𝔞 : Submodule R L) :
    Maximal (fun 𝔟 : Submodule R L' ↦ 𝔟 ≤ cartanP θ' ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0)
      (𝔞.map e.toLinearMap) ↔
    Maximal (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ cartanP θ ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞 := by
  have hpred : ∀ (𝔟 : Submodule R L),
      (𝔟.map e.toLinearMap ≤ cartanP θ' ∧
        ∀ x ∈ 𝔟.map e.toLinearMap, ∀ y ∈ 𝔟.map e.toLinearMap, ⁅x, y⁆ = 0) ↔
      (𝔟 ≤ cartanP θ ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) := fun 𝔟 ↦ by
    rw [← map_cartanP e h]
    constructor
    · rintro ⟨hle, hab⟩
      refine ⟨fun x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
      · obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp (hle (Submodule.mem_map_of_mem hx))
        exact (e.injective hze) ▸ hz
      · apply EquivLike.injective e
        rw [e.map_lie, map_zero]
        exact hab _ (Submodule.mem_map_of_mem hx) _ (Submodule.mem_map_of_mem hy)
    · rintro ⟨hle, hab⟩
      refine ⟨Submodule.map_mono hle, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [LieEquiv.coe_toLieHom, LieHom.coe_toLinearMap]
      rw [← e.map_lie, hab x hx y hy, map_zero]
  have hmap_symm : ∀ (𝔟' : Submodule R L'),
      (𝔟'.map e.symm.toLinearMap).map e.toLinearMap = 𝔟' := fun 𝔟' ↦ by
    ext y
    simp only [Submodule.mem_map, LieEquiv.coe_toLieHom, LieHom.coe_toLinearMap]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩
  have hle_iff : ∀ (𝔟₁ 𝔟₂ : Submodule R L),
      𝔟₁.map e.toLinearMap ≤ 𝔟₂.map e.toLinearMap ↔ 𝔟₁ ≤ 𝔟₂ := fun 𝔟₁ 𝔟₂ ↦ by
    constructor
    · intro hle x hx
      obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp (hle (Submodule.mem_map_of_mem hx))
      exact (e.injective hze) ▸ hz
    · exact Submodule.map_mono
  constructor
  · rintro ⟨hmem, hmax⟩
    refine ⟨(hpred 𝔞).mp hmem, fun 𝔟 h𝔟 hle ↦ ?_⟩
    exact (hle_iff 𝔟 𝔞).mp (hmax ((hpred 𝔟).mpr h𝔟) (Submodule.map_mono hle))
  · rintro ⟨hmem, hmax⟩
    refine ⟨(hpred 𝔞).mpr hmem, fun 𝔟' h𝔟' hle ↦ ?_⟩
    have h𝔟 : (𝔟'.map e.symm.toLinearMap) ≤ cartanP θ ∧
        ∀ x ∈ 𝔟'.map e.symm.toLinearMap, ∀ y ∈ 𝔟'.map e.symm.toLinearMap, ⁅x, y⁆ = 0 :=
      (hpred (𝔟'.map e.symm.toLinearMap)).mp (by rwa [hmap_symm])
    have hle' : 𝔞 ≤ 𝔟'.map e.symm.toLinearMap := by
      rw [← hle_iff, hmap_symm]
      exact hle
    have hback := hmax h𝔟 hle'
    rw [← hmap_symm 𝔟']
    exact Submodule.map_mono hback

end Intertwining

/-! ### Commuting Cartan involutions and purely algebraic conjugacy -/

namespace IsCartanInvolution

section Algebraic

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ θ' : L ≃ₗ⁅ℝ⁆ L}

/-- **Commuting Cartan involutions coincide**: if `θ` and `θ'` are Cartan involutions with
`θ ∘ θ' = θ' ∘ θ`, then `θ = θ'`. -/
theorem eq_of_commute (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ')
    (hcomm : ∀ x, θ (θ' x) = θ' (θ x)) : θ = θ' := by
  have hle : ∀ {σ τ : L ≃ₗ⁅ℝ⁆ L}, IsCartanInvolution σ → IsCartanInvolution τ →
      (∀ x, σ (τ x) = τ (σ x)) → σ.toLieHom.fixedSubalgebra ≤ τ.toLieHom.fixedSubalgebra := by
    intro σ τ hσ hτ hst x hx
    have hσx : σ x = x := LieHom.mem_fixedSubalgebra.mp hx
    have hp_k : x - τ x ∈ σ.toLieHom.fixedSubalgebra := by
      rw [LieHom.mem_fixedSubalgebra]
      simp [hσx, hst x]
    have hp_p : x - τ x ∈ cartanP τ := by
      rw [mem_cartanP]
      simp [hτ.apply_apply]
    have hp0 : x - τ x = 0 := by
      by_contra hne
      have hneg := hσ.killingForm_neg_of_mem_fixedSubalgebra hp_k hne
      have hpos := hτ.killingForm_pos_of_mem_cartanP hp_p hne
      linarith
    rw [LieHom.mem_fixedSubalgebra]
    exact (sub_eq_zero.mp hp0).symm
  exact hθ.eq_of_fixedSubalgebra_eq hθ' <|
    le_antisymm (hle hθ hθ' hcomm) (hle hθ' hθ fun x ↦ (hcomm x).symm)

/-- For two Cartan involutions `θ` and `θ'`, the squared composition `P = (θ ∘ θ')²` is
diagonalizable in a basis of `L` with strictly positive eigenvalues, and satisfies
`P (θ x) = θ (P⁻¹ x)` and `P (θ' x) = θ' (P⁻¹ x)`. -/
private theorem exists_positive_eigenbasis_sq_comp (hθ : IsCartanInvolution θ)
    (hθ' : IsCartanInvolution θ') :
    let P := (θ'.trans θ).trans (θ'.trans θ)
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ L) (μ : Fin n → ℝ),
      (∀ i, 0 < μ i) ∧
      (∀ i, P (b i) = μ i • b i) ∧
      (∀ x, P (θ x) = θ (P.symm x)) ∧
      (∀ x, P (θ' x) = θ' (P.symm x)) := by
  let _ : NormedAddCommGroup L := hθ.innerProductCore.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ L := InnerProductSpace.ofCore hθ.innerProductCore.toCore
  have _ : FiniteDimensional ℝ L := hθ.finiteDimensional
  let ω : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := ω.trans ω
  have hω_apply (x : L) : ω x = θ (θ' x) := rfl
  have hω_symm_apply (x : L) : ω.symm x = θ' (θ x) := by
    simp [ω, hθ.symm_eq_self, hθ'.symm_eq_self]
  have hP_apply (x : L) : P x = ω (ω x) := rfl
  have hP_symm_apply (x : L) : P.symm x = ω.symm (ω.symm x) := rfl
  have hω_selfAdj (x y : L) : cartanBilinForm θ (ω x) y = cartanBilinForm θ x (ω y) := by
    simp only [cartanBilinForm_apply, hω_apply]
    rw [killingForm_of_equiv_apply θ (θ' x) y, killingForm_apply_left_eq_right hθ'.apply_apply x y,
      hθ.apply_apply]
  have hP_selfAdj (x y : L) : cartanBilinForm θ (P x) y = cartanBilinForm θ x (P y) := by
    rw [hP_apply, hP_apply, hω_selfAdj, hω_selfAdj]
  have hP_symm : (P : L →ₗ[ℝ] L).IsSymmetric := fun x y ↦ by
    simpa [innerProductCore_inner] using hP_selfAdj x y
  have hP_pos {x : L} (hx : x ≠ 0) : 0 < cartanBilinForm θ (P x) x := by
    rw [hP_apply, hω_selfAdj]
    exact hθ.cartanBilinForm_pos fun h0 ↦ hx (ω.injective (by simpa using h0))
  have hθ_ω (x : L) : θ (ω x) = ω.symm (θ x) := by
    rw [hω_apply, hω_symm_apply, hθ.apply_apply, hθ.apply_apply]
  have hP_θ (x : L) : P (θ x) = θ (P.symm x) := by
    apply EquivLike.injective θ
    rw [hθ.apply_apply, hP_apply, hθ_ω, hθ_ω, hθ.apply_apply, hP_symm_apply]
  have hP_θ' (x : L) : P (θ' x) = θ' (P.symm x) := by
    simp only [hP_apply, hP_symm_apply, hω_apply, hω_symm_apply, hθ'.apply_apply]
  let n := Module.finrank ℝ L
  let b : Module.Basis (Fin n) ℝ L := (hP_symm.eigenvectorBasis rfl).toBasis
  let μ : Fin n → ℝ := hP_symm.eigenvalues rfl
  have hb_eig (i : Fin n) : P (b i) = μ i • b i := by
    simpa only [b, μ, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LieEquiv.coe_toLinearEquiv, RCLike.ofReal_real_eq_id, id_eq] using
      hP_symm.apply_eigenvectorBasis rfl i
  have hμ_pos (i : Fin n) : 0 < μ i := by
    have hpos := hP_pos (b.ne_zero i)
    rw [hb_eig i, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpos
    exact pos_of_mul_pos_left hpos (hθ.cartanBilinForm_nonneg (b i))
  exact ⟨n, b, μ, hμ_pos, hb_eig, hP_θ, hP_θ'⟩

/-- **Purely algebraic conjugacy of Cartan involutions** (Knapp, Chapter VI, Theorem 6.16): given
two Cartan involutions `θ` and `θ'` of a real Lie algebra `L`, there exist `Z ∈ cartanP θ`, a Lie
algebra automorphism `φ` conjugating `θ` to `θ'`, and a basis `b` of `L` on which `ad Z` acts
diagonally with real eigenvalues `c_i` and `φ` acts diagonally with eigenvalues `Real.exp (c_i)`. -/
theorem exists_conj_basis (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ') :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ L) (c : Fin n → ℝ) (Z : L) (φ : L ≃ₗ⁅ℝ⁆ L),
      Z ∈ cartanP θ ∧
      (∀ Y, θ' (φ Y) = φ (θ Y)) ∧
      (∀ i, ⁅Z, b i⁆ = c i • b i) ∧
      (∀ i, φ (b i) = Real.exp (c i) • b i) := by
  have _ : FiniteDimensional ℝ L := hθ.finiteDimensional
  have _ : IsKilling ℝ L := hθ.isKilling
  let P : L ≃ₗ⁅ℝ⁆ L := (θ'.trans θ).trans (θ'.trans θ)
  obtain ⟨n, b, μ, hμ_pos, hb_eig, hP_θ, hP_θ'⟩ := hθ.exists_positive_eigenbasis_sq_comp hθ'
  have hb_symm_eig (i : Fin n) : P.symm (b i) = (μ i)⁻¹ • b i := by
    apply EquivLike.injective P
    rw [P.apply_symm_apply, map_smul, hb_eig i, smul_smul, inv_mul_cancel₀ (hμ_pos i).ne', one_smul]
  -- Functional calculus `diagOp f` on the eigenbasis `b`, reusing coordinate scaling.
  let diagOp (f : ℝ → ℝ) : L →ₗ[ℝ] L := b.constr ℝ (fun i ↦ f (μ i) • b i)
  have hdiag_eig (f : ℝ → ℝ) {v : L} {c : ℝ} (hv : P v = c • v) : diagOp f v = f c • v := by
    conv_lhs => rw [← b.sum_repr v]
    conv_rhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, diagOp, Module.Basis.constr_basis, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h0 : b.repr v i = 0
    · simp [h0]
    · have hcoord := b.repr_apply_of_apply_basis (f := (P : L →ₗ[ℝ] L)) hb_eig v i
      rw [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, hv, map_smul, Finsupp.smul_apply,
        smul_eq_mul] at hcoord
      rw [mul_right_cancel₀ h0 hcoord.symm, mul_comm]
  have hdiag_bracket (f : ℝ → ℝ) (i j : Fin n) :
      diagOp f ⁅b i, b j⁆ = f (μ i * μ j) • ⁅b i, b j⁆ :=
    hdiag_eig f (by rw [P.map_lie, hb_eig i, hb_eig j, smul_lie, lie_smul, smul_smul])
  have hdiag_inv (f : ℝ → ℝ) (σ : L ≃ₗ⁅ℝ⁆ L) (hσ : ∀ x, P (σ x) = σ (P.symm x)) (x : L) :
      diagOp f (σ x) = σ (diagOp (fun t ↦ f t⁻¹) x) := by
    have hlin : (diagOp f).comp (σ : L →ₗ[ℝ] L) =
        (σ : L →ₗ[ℝ] L).comp (diagOp (fun t ↦ f t⁻¹)) :=
      b.ext fun i ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
        have heig : P (σ (b i)) = (μ i)⁻¹ • σ (b i) := by
          rw [hσ, hb_symm_eig i, map_smul]
        rw [hdiag_eig f heig]
        simp only [diagOp, Module.Basis.constr_basis, map_smul]
    exact LinearMap.congr_fun hlin x
  -- Real powers `powP s : L ≃ₗ⁅ℝ⁆ L` acting by `μ i ^ s` on `b i`.
  have hpow_lie (s : ℝ) (x y : L) :
      diagOp (· ^ s) ⁅x, y⁆ = ⁅diagOp (· ^ s) x, diagOp (· ^ s) y⁆ := by
    have h1 (i : Fin n) :
        (diagOp (· ^ s)).comp (ad ℝ L (b i)) =
          (ad ℝ L (diagOp (· ^ s) (b i))).comp (diagOp (· ^ s)) :=
      b.ext fun j ↦ by
        simp only [LinearMap.comp_apply, ad_apply]
        rw [hdiag_bracket (· ^ s) i j, Real.mul_rpow (hμ_pos i).le (hμ_pos j).le]
        simp only [diagOp, Module.Basis.constr_basis, smul_lie, lie_smul, smul_smul, mul_comm]
    have h2 :
        (diagOp (· ^ s)).comp (-(ad ℝ L y)) =
          (-(ad ℝ L (diagOp (· ^ s) y))).comp (diagOp (· ^ s)) :=
      b.ext fun i ↦ by
        simp only [LinearMap.comp_apply, LinearMap.neg_apply, ad_apply, lie_skew]
        simpa [ad_apply] using LinearMap.congr_fun (h1 i) y
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, ad_apply, lie_skew] using
      LinearMap.congr_fun h2 x
  have hpow_comp (s t : ℝ) (x : L) :
      diagOp (· ^ s) (diagOp (· ^ t) x) = diagOp (· ^ (s + t)) x := by
    have hlin : (diagOp (· ^ s)).comp (diagOp (· ^ t)) = diagOp (· ^ (s + t)) :=
      b.ext fun i ↦ by
        simp only [LinearMap.comp_apply, diagOp, Module.Basis.constr_basis, map_smul, smul_smul]
        rw [mul_comm, ← Real.rpow_add (hμ_pos i)]
    exact LinearMap.congr_fun hlin x
  have hpow_zero (x : L) : diagOp (· ^ (0 : ℝ)) x = x := by
    have hlin : diagOp (· ^ (0 : ℝ)) = LinearMap.id :=
      b.ext fun i ↦ by simp [diagOp]
    exact LinearMap.congr_fun hlin x
  have hpow_one (x : L) : diagOp (· ^ (1 : ℝ)) x = P x := by
    have hlin : diagOp (· ^ (1 : ℝ)) = (P : L →ₗ[ℝ] L) :=
      b.ext fun i ↦ by
        simp only [diagOp, Module.Basis.constr_basis, Real.rpow_one, LinearEquiv.coe_coe,
          LieEquiv.coe_toLinearEquiv]
        exact (hb_eig i).symm
    exact LinearMap.congr_fun hlin x
  let powP (s : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
    ({ toFun := diagOp (· ^ s)
       invFun := diagOp (· ^ (-s))
       map_add' := fun x y ↦ map_add (diagOp (· ^ s)) x y
       map_smul' := fun r x ↦ map_smul (diagOp (· ^ s)) r x
       left_inv := fun x ↦ by rw [hpow_comp, neg_add_cancel, hpow_zero]
       right_inv := fun x ↦ by rw [hpow_comp, add_neg_cancel, hpow_zero]
       map_lie' := fun {x y} ↦ hpow_lie s x y })
  have hpowP_apply (s : ℝ) (x : L) : powP s x = diagOp (· ^ s) x := rfl
  have hpowP_symm_apply (s : ℝ) (x : L) : (powP s).symm x = powP (-s) x := rfl
  have hpowP_comp (s t : ℝ) (x : L) : powP s (powP t x) = powP (s + t) x := hpow_comp s t x
  have hpowP_zero (x : L) : powP 0 x = x := hpow_zero x
  have hpowP_one (x : L) : powP 1 x = P x := hpow_one x
  have hpowP_inv (s : ℝ) (σ : L ≃ₗ⁅ℝ⁆ L) (hσ : ∀ x, P (σ x) = σ (P.symm x)) (x : L) :
      powP s (σ x) = σ (powP (-s) x) := by
    rw [hpowP_apply, hpowP_apply]
    have h := hdiag_inv (· ^ s) σ hσ x
    have hfun : (fun t : ℝ ↦ t⁻¹ ^ s) = (· ^ (-s)) :=
      funext fun t ↦ (Real.rpow_neg_eq_inv_rpow t s).symm
    simpa only [hfun] using h
  -- Set `φ = powP (-1 / 4)` and show `(φ.symm.trans θ).trans φ = θ'`.
  let φ : L ≃ₗ⁅ℝ⁆ L := powP (-1 / 4)
  let θ₁ : L ≃ₗ⁅ℝ⁆ L := (φ.symm.trans θ).trans φ
  have hθ₁_apply (x : L) : θ₁ x = powP (-1 / 2) (θ x) := by
    simp only [θ₁, φ, LieEquiv.trans_apply, hpowP_symm_apply]
    rw [← hpowP_inv (-1 / 4) θ hP_θ, hpowP_comp]
    norm_num
  have hθ₁_comm (x : L) : θ₁ (θ' x) = θ' (θ₁ x) := by
    apply EquivLike.injective (powP (1 / 2))
    rw [hθ₁_apply (θ' x), hθ₁_apply x, hpowP_comp, hpowP_inv (1 / 2) θ' hP_θ']
    have hhalf : (1 / 2 : ℝ) + -1 / 2 = 0 := by norm_num
    rw [hhalf, hpowP_zero, hpowP_comp]
    have hneg_one : -(1 / 2 : ℝ) + -1 / 2 = -1 := by norm_num
    rw [hneg_one, ← hpowP_inv 1 θ' hP_θ', hpowP_one, hP_θ']
    simp [hθ.symm_eq_self, hθ'.symm_eq_self, hθ.apply_apply, hθ'.apply_apply]
  have hθ₁_eq : θ₁ = θ' := (hθ.conj φ).eq_of_commute hθ' hθ₁_comm
  have hconj (Y : L) : θ' (φ Y) = φ (θ Y) := by
    rw [← hθ₁_eq]
    simp [θ₁]
  -- Build the Lie derivation `logP = diagOp Real.log`, realize it as `ad Z₀`, and verify `Z₀ ∈ 𝔭`.
  have hlog_der (x y : L) :
      diagOp Real.log ⁅x, y⁆ = ⁅diagOp Real.log x, y⁆ + ⁅x, diagOp Real.log y⁆ := by
    have h1 (i : Fin n) :
        (diagOp Real.log).comp (ad ℝ L (b i)) =
          ad ℝ L (diagOp Real.log (b i)) + (ad ℝ L (b i)).comp (diagOp Real.log) :=
      b.ext fun j ↦ by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, ad_apply]
        rw [hdiag_bracket Real.log i j, Real.log_mul (hμ_pos i).ne' (hμ_pos j).ne', add_smul]
        simp only [diagOp, Module.Basis.constr_basis, smul_lie, lie_smul]
    have h2 :
        (diagOp Real.log).comp (-(ad ℝ L y)) =
          (-(ad ℝ L y)).comp (diagOp Real.log) + (-(ad ℝ L (diagOp Real.log y))) :=
      b.ext fun i ↦ by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply, ad_apply,
          lie_skew]
        simpa [ad_apply] using LinearMap.congr_fun (h1 i) y
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply, ad_apply,
      lie_skew] using LinearMap.congr_fun h2 x
  let logP : LieDerivation ℝ L L :=
    ⟨diagOp Real.log, fun a b ↦ by rw [hlog_der, sub_eq_add_neg, lie_skew, add_comm]⟩
  have hlogP_θ (x : L) : logP (θ x) = -θ (logP x) := by
    have h := hdiag_inv Real.log θ hP_θ x
    have hneg : diagOp (fun t ↦ Real.log t⁻¹) = -diagOp Real.log :=
      b.ext fun i ↦ by simp [diagOp, Real.log_inv]
    rw [hneg, LinearMap.neg_apply, map_neg] at h
    exact h
  obtain ⟨Z₀, hZ₀⟩ := LieDerivation.IsKilling.exists_eq_ad logP
  have hZ₀_ad (x : L) : ⁅Z₀, x⁆ = logP x := by
    have h := LinearMap.congr_fun (congrArg LieDerivation.toLinearMap hZ₀) x
    simpa [LieDerivation.coe_ad_apply_eq_ad_apply] using h
  have hZ₀_mem : Z₀ ∈ cartanP θ := by
    rw [mem_cartanP, ← add_eq_zero_iff_eq_neg]
    have hmem : θ Z₀ + Z₀ ∈ center ℝ L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro y
      rw [← neg_eq_zero, lie_skew, add_lie]
      have h1 : ⁅θ Z₀, y⁆ = -⁅Z₀, y⁆ := by
        calc
          ⁅θ Z₀, y⁆ = ⁅θ Z₀, θ (θ y)⁆ := by rw [hθ.apply_apply]
          _ = θ ⁅Z₀, θ y⁆ := (θ.map_lie Z₀ (θ y)).symm
          _ = θ (logP (θ y)) := by rw [hZ₀_ad]
          _ = θ (-θ (logP y)) := by rw [hlogP_θ]
          _ = -logP y := by rw [map_neg, hθ.apply_apply]
          _ = -⁅Z₀, y⁆ := by rw [hZ₀_ad]
      rw [h1, neg_add_cancel]
    rw [hθ.center_eq_bot] at hmem
    exact hmem
  -- Set `Z = (-1/4) • Z₀ ∈ cartanP θ` and `c i = (-1/4) * log (μ i)`.
  refine ⟨n, b, fun i ↦ (-1 / 4 : ℝ) * Real.log (μ i), (-1 / 4 : ℝ) • Z₀, φ,
    (cartanP θ).smul_mem (-1 / 4 : ℝ) hZ₀_mem, hconj, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [smul_lie, hZ₀_ad]
    simp [logP, diagOp, smul_smul]
  · simp only [φ, hpowP_apply, diagOp, Module.Basis.constr_basis]
    rw [Real.rpow_def_of_pos (hμ_pos i), mul_comm]

/-- **Conjugacy of Cartan involutions** (purely algebraic form): any two Cartan involutions `θ` and
`θ'` of a real Lie algebra are conjugate by a Lie algebra automorphism. -/
theorem exists_lieEquiv_conj (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ') :
    ∃ φ : L ≃ₗ⁅ℝ⁆ L, (φ.symm.trans θ).trans φ = θ' := by
  obtain ⟨_, _, _, _, φ, _, hconj, _, _⟩ := hθ.exists_conj_basis hθ'
  refine ⟨φ, LieEquiv.ext fun x ↦ ?_⟩
  simp only [LieEquiv.trans_apply]
  rw [← hconj (φ.symm x), φ.apply_symm_apply]

end Algebraic

/-! ### Inner exponential conjugacy via any normed model -/

section Normed

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {L E : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {θ θ' : L ≃ₗ⁅ℝ⁆ L}

/-- **Inner conjugacy of Cartan involutions**: transported along any linear equivalence
`e : L ≃ₗ[ℝ] E` into a finite-dimensional real normed space, any two Cartan involutions `θ` and
`θ'` are conjugate by `exp (e.conj (ad Z))` for some `Z ∈ cartanP θ`. Taking `e = LinearEquiv.refl`
recovers direct operator-exponential conjugacy on any concrete normed Lie algebra (such as
`LeftInvariantDerivation I G` or a matrix Lie algebra) without norm-instance diamonds. -/
theorem exists_exp_ad_conj_of_linearEquiv (hθ : IsCartanInvolution θ)
    (hθ' : IsCartanInvolution θ') (e : L ≃ₗ[ℝ] E) :
    ∃ Z ∈ cartanP θ, ∀ Y : L,
      θ' (e.symm (NormedSpace.exp
        (LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))) (e Y))) =
      e.symm (NormedSpace.exp
        (LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))) (e (θ Y))) := by
  have _ : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨n, b, c, Z, φ, hZ, hconj, had_b, hφ_b⟩ := hθ.exists_conj_basis hθ'
  let A : E →L[ℝ] E := LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))
  have hexp_eq : (NormedSpace.exp A : E →L[ℝ] E).toLinearMap = e.conj φ.toLinearMap := by
    refine (b.map e).ext fun i ↦ ?_
    have hAi : A (e (b i)) = c i • e (b i) := by
      simp [A, LinearEquiv.conj_apply, LieAlgebra.ad_apply, had_b i]
    have hexp_i := ContinuousLinearMap.exp_apply_of_apply_eq_smul A hAi
    rw [← Real.exp_eq_exp_ℝ] at hexp_i
    simpa [LinearEquiv.conj_apply, hφ_b i] using hexp_i
  refine ⟨Z, hZ, fun Y ↦ ?_⟩
  have hact (X : L) : e.symm (NormedSpace.exp A (e X)) = φ X := by
    have h := LinearMap.congr_fun hexp_eq (e X)
    simpa [LinearEquiv.conj_apply] using congrArg e.symm h
  rw [hact Y, hact (θ Y), hconj Y]

end Normed

end IsCartanInvolution

end TauCeti
