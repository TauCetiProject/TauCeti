/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.Eigenspace.Transport
import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Unitary Clifford intertwiners and Hermitian half-spinors

A real Clifford algebra map `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W` into the complex
endomorphisms of `W` extends uniquely to a complex algebra homomorphism
`CliffordAlgebra.complexifyAction ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ W`.
When `Q` is nondegenerate on a real space of even dimension `2 * m` and `W` has complex dimension
`2 ^ m`, the complexified Clifford algebra is simple of dimension `4 ^ m = (dim_ℂ W)²`, so
`complexifyAction ρ` is an algebra isomorphism onto `Module.End ℂ W`.

Combining this fullness criterion with the Skolem–Noether theorem for endomorphism algebras and
Schur's lemma for compatible Hermitian metrics
(`CliffordAlgebra.existsUnique_pos_mul_inner_of_surjective`) classifies unitary Clifford
intertwiners along linear isometries `f : V ≃ₗᵢ[ℝ] V'`:

* **Existence** (`CliffordAlgebra.exists_unitary_intertwiner_of_finrank_eq`): for negative-definite
  norm-square forms in dimension `2 * m`, any two Hermitian Clifford modules of complex dimension
  `2 ^ m` are intertwined along `f` by a complex linear isometry equivalence `U : W ≃ₗᵢ[ℂ] W'`.
* **Uniqueness up to a phase** (`CliffordAlgebra.existsUnique_circle_smul_intertwiner`): whenever
  `complexifyAction ρ` is surjective on a nontrivial module `W`, any two unitary intertwiners along
  `f` differ by multiplication by a unique element of `Circle`.

In dimension four, the chirality element `Γ` splits any Clifford module with `Q v = -‖v‖²` into
complementary `±1` eigenspaces of equal complex dimension
(`CliffordAlgebra.isCompl_eigenspace_chirality`,
`CliffordAlgebra.finrank_eq_two_mul_finrank_positiveHalfSpinors`), which are mutually orthogonal
when the generators act skew-adjointly
(`CliffordAlgebra.inner_eq_zero_of_mem_eigenspace_chirality`). Consequently half-spin rank two
(`dim_ℂ W⁺ = 2`) implies `dim_ℂ W = 4`, making `complexifyAction ρ` bijective. Every unitary
Clifford intertwiner along an orientation-preserving isometry restricts to unitary equivalences on
all chirality eigenspaces (`CliffordAlgebra.halfSpinLinearIsometryEquiv`) that intertwine odd
Clifford multiplication (`CliffordAlgebra.halfSpinCliffordMul`), and the induced conjugation of
linear maps between chirality eigenspaces is independent of the choice of unitary intertwiner
because the `Circle` phase cancels (`CliffordAlgebra.conj_halfSpinLinearIsometryEquiv_eq`).

## Main definitions

* `CliffordAlgebra.complexifyAction ρ`: the `ℂ`-algebra extension of `ρ : CliffordAlgebra Q →ₐ[ℝ]
  Module.End ℂ W` to `CliffordAlgebra (Q.baseChange ℂ)`.
* `CliffordAlgebra.halfSpinLinearIsometryEquiv`: the restriction of a unitary Clifford intertwiner
  along an orientation-preserving four-dimensional isometry to the `ε`-eigenspaces of `Γ`.

## Main results

* `CliffordAlgebra.complexifyAction_bijective_of_finrank_eq`: fullness in even dimension `2 * m` at
  spinor dimension `2 ^ m`.
* `CliffordAlgebra.existsUnique_circle_smul_intertwiner` and
  `CliffordAlgebra.exists_unitary_intertwiner_of_finrank_eq`: `Circle`-torsor classification of
  unitary Clifford intertwiners.
* `CliffordAlgebra.adjoint_evenHalfSpinAction`,
  `CliffordAlgebra.coe_adjoint_halfSpinCliffordMul_apply`, and
  `CliffordAlgebra.norm_halfSpinCliffordMul_apply`: adjoint and norm laws for the even half-spin
  action and chiral Clifford multiplication.
* `CliffordAlgebra.conj_halfSpinLinearIsometryEquiv_eq`: canonical conjugation of operators between
  chirality eigenspaces, independent of the chosen unitary intertwiner.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace TensorProduct ComplexOrder

/-! ### Complexifying a real Clifford action on a complex vector space -/

section Complexify

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [AddCommGroup W] [Module ℂ W]

/-- **Complexification of a real Clifford action** on a complex vector space: the unique
`ℂ`-algebra homomorphism out of `CliffordAlgebra (Q.baseChange ℂ)` extending
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W` along `CliffordAlgebra.ofBaseChangeAux ℂ Q`. -/
def complexifyAction (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) :
    CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ W :=
  (Algebra.TensorProduct.lift (Algebra.ofId ℂ (Module.End ℂ W)) ρ
    fun z x ↦ by rw [Commute, SemiconjBy, Algebra.ofId_apply, Algebra.commutes]).comp
      (toBaseChange ℂ Q)

/-- `complexifyAction ρ` extends `ρ` along `ofBaseChangeAux ℂ Q`. -/
@[simp]
theorem complexifyAction_ofBaseChangeAux (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (x : CliffordAlgebra Q) :
    complexifyAction ρ (ofBaseChangeAux ℂ Q x) = ρ x := by
  have h : toBaseChange ℂ Q (ofBaseChangeAux ℂ Q x) = 1 ⊗ₜ[ℝ] x := by
    have h1 : ofBaseChange ℂ Q (1 ⊗ₜ[ℝ] x) = ofBaseChangeAux ℂ Q x :=
      (Algebra.TensorProduct.lift_tmul _ _ _ 1 x).trans (by rw [map_one, one_mul])
    rw [← h1, toBaseChange_ofBaseChange]
  rw [complexifyAction, AlgHom.comp_apply, h]
  exact (Algebra.TensorProduct.lift_tmul _ _ _ 1 x).trans (by rw [map_one, one_mul])

/-- On complexified vector generators, `complexifyAction ρ` scales the real Clifford action. -/
@[simp]
theorem complexifyAction_ι_tmul (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (z : ℂ) (v : V) :
    complexifyAction ρ (ι (Q.baseChange ℂ) (z ⊗ₜ v)) = z • ρ (ι Q v) := by
  have h : ι (Q.baseChange ℂ) (z ⊗ₜ v) = z • ofBaseChangeAux ℂ Q (ι Q v) := by
    rw [ofBaseChangeAux_ι, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, complexifyAction_ofBaseChangeAux]

/-- Naturality of `complexifyAction` under quadratic isometries. -/
theorem complexifyAction_comp_map {V' : Type*} [AddCommGroup V'] [Module ℝ V']
    {Q' : QuadraticForm ℝ V'} (f : Q →qᵢ Q') (ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W) :
    (complexifyAction ρ').comp (CliffordAlgebra.map (f.baseChange ℂ)) =
      complexifyAction (ρ'.comp (CliffordAlgebra.map f)) := by
  refine CliffordAlgebra.hom_ext ?_
  ext v
  simp

/-- **Fullness of spinor actions in even dimension.** When `Q` is nondegenerate on a real space of
dimension `2 * m` and `W` has complex dimension `2 ^ m`, the complexified Clifford action
`complexifyAction ρ` is bijective onto `Module.End ℂ W`. -/
theorem complexifyAction_bijective_of_finrank_eq [FiniteDimensional ℝ V] [FiniteDimensional ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (hQnd : Q.Nondegenerate) {m : ℕ}
    (hV : finrank ℝ V = 2 * m) (hW : finrank ℂ W = 2 ^ m) :
    Function.Bijective (complexifyAction ρ) := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; positivity)
  have hsimple : IsSimpleRing (CliffordAlgebra (Q.baseChange ℂ)) :=
    isSimpleRing_of_even_finrank (QuadraticForm.Nondegenerate.baseChange (L := ℂ) hQnd)
      ⟨m, by rw [Module.finrank_baseChange, hV]; ring⟩
  have hinj : Function.Injective (complexifyAction ρ) :=
    (complexifyAction ρ).toRingHom.injective
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (complexifyAction ρ).toLinearMap) ?_).mp hinj⟩
  rw [finrank_eq_two_pow, Module.finrank_baseChange, hV, Module.finrank_linearMap, hW, pow_mul']
  ring

end Complexify

/-! ### Unitary Clifford intertwiners: uniqueness up to `Circle` and existence -/

section Intertwiners

variable {V V' W W' : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [AddCommGroup V'] [Module ℝ V'] {Q' : QuadraticForm ℝ V'}

/-- If a `ℂ`-linear endomorphism of `W` commutes with `ρ (ι Q v)` for every `v : V`, then it
commutes with `complexifyAction ρ a` for every `a` in the complexified Clifford algebra. -/
private theorem commute_complexifyAction_of_forall_ι [AddCommGroup W] [Module ℂ W]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {A : Module.End ℂ W}
    (hA : ∀ v, A ∘ₗ ρ (ι Q v) = ρ (ι Q v) ∘ₗ A) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    Commute A (complexifyAction ρ a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    rw [AlgHom.commutes]
    exact (Algebra.commutes z A).symm
  | ι w =>
    induction w using TensorProduct.inductionOn with
    | tmul z v =>
      rw [complexifyAction_ι_tmul]
      exact Commute.smul_right
        ((mul_eq_comp A _).trans ((hA v).trans (mul_eq_comp _ A).symm)) z
    | add x y hx hy =>
      rw [map_add, map_add]
      exact hx.add_right hy
  | mul x y hx hy =>
    rw [map_mul]
    exact hx.mul_right hy
  | add x y hx hy =>
    rw [map_add]
    exact hx.add_right hy

/-- **Uniqueness of unitary Clifford intertwiners up to `Circle`.** If `complexifyAction ρ` is
surjective onto `Module.End ℂ W` on a nontrivial complex inner product space `W`, any two unitary
intertwiners `U₁, U₂ : W ≃ₗᵢ[ℂ] W'` along a map `f : V → V'` differ by a unique phase in `Circle`.
-/
theorem existsUnique_circle_smul_intertwiner [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Nontrivial W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
    (hsurj : Function.Surjective (complexifyAction ρ)) {f : V → V'}
    (U₁ U₂ : W ≃ₗᵢ[ℂ] W')
    (hU₁ : ∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap)
    (hU₂ : ∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) :
    ∃! z : Circle, ∀ w, U₂ w = (z : ℂ) • U₁ w := by
  let L : W ≃ₗᵢ[ℂ] W := U₂.trans U₁.symm
  have hU₁L (w : W) : U₁ (L w) = U₂ w := U₁.apply_symm_apply (U₂ w)
  have hcomm_ι (v : V) : L.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ (ι Q v) ∘ₗ L.toLinearEquiv.toLinearMap := by
    ext w
    apply U₁.injective
    change U₁ (L (ρ (ι Q v) w)) = U₁ (ρ (ι Q v) (L w))
    have h₁ : U₁ (ρ (ι Q v) (L w)) = ρ' (ι Q' (f v)) (U₁ (L w)) :=
      LinearMap.congr_fun (hU₁ v) (L w)
    have h₂ : U₂ (ρ (ι Q v) w) = ρ' (ι Q' (f v)) (U₂ w) :=
      LinearMap.congr_fun (hU₂ v) w
    rw [hU₁L, h₂, h₁, hU₁L]
  have hcenter : L.toLinearEquiv.toLinearMap ∈ Subalgebra.center ℂ (Module.End ℂ W) := by
    rw [Subalgebra.mem_center_iff]
    intro B
    obtain ⟨a, rfl⟩ := hsurj B
    exact (commute_complexifyAction_of_forall_ι hcomm_ι a).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hcenter
  have hLw (w : W) : L w = c • w := by
    have hcw := LinearMap.congr_fun hc w
    rwa [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self] at hcw
  let := NormedSpace.restrictScalars ℝ ℂ W
  obtain ⟨u, hu⟩ := exists_norm_eq W zero_le_one
  have hc_norm : ‖c‖ = 1 := by
    have hnorm := L.norm_map u
    rwa [hLw, norm_smul, hu, mul_one] at hnorm
  refine ⟨⟨c, mem_sphere_zero_iff_norm.mpr hc_norm⟩, fun w ↦ ?_, fun z hz ↦ ?_⟩
  · calc
      U₂ w = U₁ (L w) := (hU₁L w).symm
      _ = c • U₁ w := by rw [hLw, map_smul]
  · ext
    have hzu : ((z : ℂ) - c) • U₁ u = 0 := by
      rw [sub_smul, ← hz u, ← map_smul, ← hLw u, hU₁L, sub_self]
    have hu₁ : U₁ u ≠ 0 := by
      intro h0
      have hnorm₁ := U₁.norm_map u
      simp [h0, hu] at hnorm₁
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzu).resolve_right hu₁)

/-- Rescaling a linear equivalence that scales the inner product by a positive real constant `r`
yields a linear isometry equivalence. -/
private def rescaleLinearIsometryEquiv [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] (T : W ≃ₗ[ℂ] W') {r : ℝ} (hr : 0 < r)
    (hT : ∀ x y, ⟪T x, T y⟫_ℂ = (r : ℂ) * ⟪x, y⟫_ℂ) : W ≃ₗᵢ[ℂ] W' where
  toFun x := (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • T x
  invFun y := ((Real.sqrt r : ℝ) : ℂ) • T.symm y
  map_add' x y := by simp [smul_add]
  map_smul' c x := by simp [smul_smul, mul_comm]
  left_inv x := by
    have hne : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hr)
    dsimp only
    rw [T.symm.map_smul, T.symm_apply_apply, smul_smul, Complex.ofReal_inv,
      mul_inv_cancel₀ hne, one_smul]
  right_inv y := by
    have hne : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hr)
    dsimp only
    rw [T.map_smul, T.apply_symm_apply, smul_smul, Complex.ofReal_inv,
      inv_mul_cancel₀ hne, one_smul]
  norm_map' x := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    have hinner := hT x x
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    have hreal : ‖T x‖ ^ 2 = r * ‖x‖ ^ 2 := Complex.ofReal_injective (by simpa using hinner)
    calc
      ‖(((Real.sqrt r)⁻¹ : ℝ) : ℂ) • T x‖ ^ 2 = ((Real.sqrt r)⁻¹) ^ 2 * ‖T x‖ ^ 2 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = ((Real.sqrt r)⁻¹) ^ 2 * (r * ‖x‖ ^ 2) := by rw [hreal]
      _ = ‖x‖ ^ 2 := by
        rw [inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel_left₀ hr.ne']

/-- **Existence of unitary Clifford intertwiners.** Let `V` and `V'` be real inner product spaces
of even dimension `2 * m` with negative norm-square forms `Q` and `Q'`, and let `f : V ≃ₗᵢ[ℝ] V'`
be a linear isometry. Any two Hermitian Clifford modules `(W, ρ)` and `(W', ρ')` of complex
dimension `2 ^ m` are intertwined along `f` by a complex linear isometry equivalence
`U : W ≃ₗᵢ[ℂ] W'`. -/
theorem exists_unitary_intertwiner_of_finrank_eq
    {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)
    (f : V ≃ₗᵢ[ℝ] V') {m : ℕ} (hV : finrank ℝ V = 2 * m)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hρ' : ∀ v, LinearMap.adjoint (ρ' (ι Q' v)) = -ρ' (ι Q' v))
    (hW : finrank ℂ W = 2 ^ m) (hW' : finrank ℂ W' = 2 ^ m) :
    ∃ U : W ≃ₗᵢ[ℂ] W', ∀ v,
      U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
        ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  have : FiniteDimensional ℝ V' := f.toLinearEquiv.finiteDimensional
  have hQnd : Q.Nondegenerate := QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by
    simpa [hQ] using hv
  have hQ'nd : Q'.Nondegenerate := QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by
    simpa [hQ'] using hv
  let eQ : Q.IsometryEquiv Q' :=
    { f.toLinearEquiv with map_app' v := by simp [hQ', hQ] }
  let eCl : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] CliffordAlgebra (Q'.baseChange ℂ) :=
    AlgEquiv.ofAlgHom (CliffordAlgebra.map (eQ.toIsometry.baseChange ℂ))
      (CliffordAlgebra.map (eQ.symm.toIsometry.baseChange ℂ))
      (CliffordAlgebra.hom_ext <| by ext v; simp [eQ])
      (CliffordAlgebra.hom_ext <| by ext v; simp [eQ])
  let α := AlgEquiv.ofBijective (complexifyAction ρ)
    (complexifyAction_bijective_of_finrank_eq ρ hQnd hV hW)
  let α' := AlgEquiv.ofBijective (complexifyAction ρ')
    (complexifyAction_bijective_of_finrank_eq ρ' hQ'nd
      (f.toLinearEquiv.finrank_eq.symm.trans hV) hW')
  obtain ⟨T, hT⟩ := (α.symm.trans (eCl.trans α')).eq_linearEquivConjAlgEquiv
  have hT_ι (v : V) (w : W) : T (ρ (ι Q v) w) = ρ' (ι Q' (f v)) (T w) := by
    have h := congr($hT (α (ι (Q.baseChange ℂ) (1 ⊗ₜ v))) (T w))
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, LinearEquiv.conjAlgEquiv_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
    have h' : T (ρ (ι Q v) w) = ρ' (ι Q' (eQ v)) (T w) := by
      simpa [α, α', eCl] using h.symm
    exact h'
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; positivity)
  let H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp T.toLinearMap).compl₂ T.toLinearMap
  have hH_apply (a b : W) : H a b = ⟪T a, T b⟫_ℂ := rfl
  obtain ⟨r, ⟨hr, hrH⟩, _⟩ := existsUnique_pos_mul_inner_of_surjective (complexifyAction ρ)
    α.surjective (fun v ↦ by simpa using hρ v) H
    ⟨fun x ↦ by rw [hH_apply, inner_self_eq_norm_sq_to_K]; positivity⟩
    (fun x hx h0 ↦
      hx <| T.injective ((inner_self_eq_zero.mp (hH_apply x x ▸ h0)).trans T.map_zero.symm))
    (fun v x y ↦ by
      rw [hH_apply, hH_apply, complexifyAction_ι_tmul, one_smul, hT_ι,
        ← LinearMap.adjoint_inner_right, hρ', LinearMap.neg_apply, inner_neg_right, ← hT_ι])
  refine ⟨rescaleLinearIsometryEquiv T hr hrH, fun v ↦ ?_⟩
  ext w
  change (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • T (ρ (ι Q v) w) =
    ρ' (ι Q' (f v)) ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • T w)
  rw [hT_ι, map_smul]

end Intertwiners

/-! ### Chirality decomposition, Hermitian half-spinors, and unitary restrictions in dimension 4 -/

section DimensionFour

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- `positiveHalfSpinors o ρ` is the `+1`-eigenspace of `ρ (chirality Q o)`. -/
theorem positiveHalfSpinors_eq_eigenspace {K W : Type*} [CommRing K] [Algebra ℝ K]
    [AddCommGroup W] [Module ℝ W] [Module K W] [IsScalarTower ℝ K W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W) :
    positiveHalfSpinors o ρ = eigenspace (ρ (chirality Q o)) 1 := by
  ext ψ
  rw [mem_positiveHalfSpinors, mem_eigenspace_iff, one_smul]

/-- **The chirality decomposition on a real Clifford module**: when `Q v = -‖v‖²`, every complex
Clifford module `W` splits as the direct sum of `positiveHalfSpinors o ρ` and the `-1`-eigenspace
of `Γ`. -/
theorem isCompl_eigenspace_chirality {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    IsCompl (positiveHalfSpinors o ρ) (eigenspace (ρ (chirality Q o)) (-1)) := by
  rw [positiveHalfSpinors_eq_eigenspace]
  exact TauCeti.isCompl_eigenspace_one_neg_one (two_ne_zero : (2 : ℂ) ≠ 0).isUnit fun w ↦ by
    rw [← mul_apply_eq_comp, ← map_mul, chirality_mul_self o hQ, map_one, one_apply_eq_self]

/-- **Total spinor dimension is twice the positive half-spinor dimension.** -/
theorem finrank_eq_two_mul_finrank_positiveHalfSpinors {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    finrank ℂ W = 2 * finrank ℂ (positiveHalfSpinors o ρ) := by
  have hsum := (Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_chirality o ρ hQ)).symm
  rw [hsum, positiveHalfSpinors_eq_eigenspace, finrank_eigenspace_chirality_neg o ρ 1, two_mul]

/-- **Half-spin rank two forces fullness of the complexified Clifford action** in dimension four. -/
theorem complexifyAction_bijective_of_finrank_positiveHalfSpinors_eq_two
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) :
    Function.Bijective (complexifyAction ρ) := by
  have hQnd : Q.Nondegenerate := QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by
    simpa [hQ] using hv
  refine complexifyAction_bijective_of_finrank_eq ρ hQnd (m := 2)
    (Fact.out : finrank ℝ V = 4) ?_
  rw [finrank_eq_two_mul_finrank_positiveHalfSpinors o ρ hQ, h₂]
  rfl

section HermitianModule

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- Distinct eigenspaces of `Γ` on a Hermitian Clifford module are mutually orthogonal; in
particular `W⁺` and `W⁻` are orthogonal. -/
theorem inner_eq_zero_of_mem_eigenspace_chirality
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ε₁ ε₂ : ℂ} (hε : ε₁ ≠ ε₂)
    {ψ₁ ψ₂ : W} (hψ₁ : ψ₁ ∈ eigenspace (ρ (chirality Q o)) ε₁)
    (hψ₂ : ψ₂ ∈ eigenspace (ρ (chirality Q o)) ε₂) :
    ⟪ψ₁, ψ₂⟫_ℂ = 0 := by
  have hsymm : (ρ (chirality Q o)).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (isSelfAdjoint_map_chirality o hρ)
  exact hsymm.orthogonalFamily_eigenspaces hε ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩

/-- **Adjoint of chiral Clifford multiplication**: for skew-adjoint generators, the adjoint of
`halfSpinCliffordMul o ρ ε v : W^ε → W^{-ε}` acts in the ambient module as `-c(v)`. -/
@[simp]
theorem coe_adjoint_halfSpinCliffordMul_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V)
    (χ : eigenspace (ρ (chirality Q o)) (-ε)) :
    (LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) χ : W) = -ρ (ι Q v) χ := by
  let A : eigenspace (ρ (chirality Q o)) (-ε) →ₗ[ℂ] eigenspace (ρ (chirality Q o)) ε :=
    { toFun η := ⟨-ρ (ι Q v) η, Submodule.neg_mem _
        (by simpa only [neg_neg] using map_ι_apply_mem_eigenspace_chirality_neg o η.2 v)⟩
      map_add' η₁ η₂ := Subtype.ext (by simp only [Submodule.coe_add, map_add, neg_add])
      map_smul' c η := Subtype.ext (by simp only [SetLike.val_smul, map_smul, smul_neg,
        RingHom.id_apply]) }
  have hA : LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) = A := by
    symm
    refine (LinearMap.eq_adjoint_iff A (halfSpinCliffordMul o ρ ε v)).mpr fun η ψ ↦ ?_
    rw [Submodule.coe_inner, Submodule.coe_inner, coe_halfSpinCliffordMul_apply_apply]
    change ⟪-ρ (ι Q v) (η : W), (ψ : W)⟫_ℂ = ⟪(η : W), ρ (ι Q v) (ψ : W)⟫_ℂ
    rw [inner_neg_left, ← LinearMap.adjoint_inner_right, hρ, LinearMap.neg_apply, inner_neg_right,
      neg_neg]
  rw [hA]
  rfl

/-- **Norm law for chiral Clifford multiplication**: for `Q v = -‖v‖²` and skew-adjoint generators,
`halfSpinCliffordMul` scales spinor norms by `‖v‖`. -/
theorem norm_halfSpinCliffordMul_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ‖halfSpinCliffordMul o ρ ε v ψ‖ = ‖v‖ * ‖ψ‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe (x := ψ), coe_halfSpinCliffordMul_apply_apply]
  exact norm_map_ι_apply hQ hρ v ψ

/-- Composing chiral Clifford multiplication with its adjoint multiplies by `‖v‖²`. -/
@[simp]
theorem adjoint_halfSpinCliffordMul_comp_self (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V) :
    LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) ∘ₗ halfSpinCliffordMul o ρ ε v =
      ((‖v‖ : ℂ) ^ 2) • LinearMap.id := by
  ext ψ
  rw [LinearMap.comp_apply, coe_adjoint_halfSpinCliffordMul_apply o hρ,
    coe_halfSpinCliffordMul_apply_apply, ← mul_apply_eq_comp, ← map_mul, ι_sq_scalar,
    hQ, map_neg, map_neg, AlgHom.commutes, LinearMap.neg_apply, neg_neg,
    Module.algebraMap_end_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
    ← Complex.ofReal_pow, Complex.coe_smul]

/-- **Adjoint of the even half-spin action**: for skew-adjoint generators, the adjoint of
`evenHalfSpinAction o ρ ε x` on any chirality eigenspace is `evenHalfSpinAction o ρ ε` evaluated at
`reverseEven Q x`. -/
@[simp]
theorem adjoint_evenHalfSpinAction (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (ε : ℂ) (x : even Q) :
    LinearMap.adjoint (evenHalfSpinAction o ρ ε x) =
      evenHalfSpinAction o ρ ε (reverseEven Q x) := by
  symm
  refine (LinearMap.eq_adjoint_iff _ _).mpr fun η ψ ↦ ?_
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_evenHalfSpinAction_apply,
    coe_evenHalfSpinAction_apply, coe_reverseEven_apply, reverse_eq_star_of_mem_even,
    ← adjoint_map_eq_map_star hρ, LinearMap.adjoint_inner_left]

end HermitianModule

/-! ### Unitary half-spin restrictions and `Circle`-independence of operator transport -/

section HalfSpinIntertwiner

variable {V' W W' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [Fact (finrank ℝ V' = 4)] {Q' : QuadraticForm ℝ V'}
  {o} (o' : Orientation ℝ V' (Fin 4))
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
  {f : V ≃ₗᵢ[ℝ] V'} (ho : o.map (Fin 4) f.toLinearEquiv = o')

/-- **Unitary restriction of a Clifford intertwiner to a chirality eigenspace**: a unitary
equivalence `U : W ≃ₗᵢ[ℂ] W'` intertwining the real generators along an orientation-preserving
linear isometry `f : V ≃ₗᵢ[ℝ] V'` restricts to a unitary equivalence on the `ε`-eigenspaces of `Γ`
for every `ε : ℂ`. -/
def halfSpinLinearIsometryEquiv {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ) :
    eigenspace (ρ (chirality Q o)) ε ≃ₗᵢ[ℂ] eigenspace (ρ' (chirality Q' o')) ε where
  toLinearEquiv := U.toLinearEquiv.ofSubmodules _ _ <| by
    have hΓ := comp_chirality_eq_chirality_comp ho hU
    rw [TauCeti.eigenspace_eq_comap_of_intertwine (e := U.toLinearEquiv)
      (LinearMap.congr_fun hΓ) ε]
    exact Submodule.map_comap_eq_of_surjective U.surjective _
  norm_map' ψ := U.norm_map ψ

/-- Coercion to the ambient spinor space commutes with `halfSpinLinearIsometryEquiv`. -/
@[simp]
theorem coe_halfSpinLinearIsometryEquiv_apply {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinLinearIsometryEquiv o' ho hU ε ψ : W') = U ψ :=
  (rfl)

/-- Coercion to the ambient spinor space commutes with `(halfSpinLinearIsometryEquiv ...).symm`. -/
@[simp]
theorem coe_halfSpinLinearIsometryEquiv_symm_apply {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ)
    (ψ : eigenspace (ρ' (chirality Q' o')) ε) :
    ((halfSpinLinearIsometryEquiv o' ho hU ε).symm ψ : W) = U.symm ψ :=
  (rfl)

/-- The unitary half-spin restriction intertwines odd Clifford multiplication `halfSpinCliffordMul`
along the vector isometry `f`. -/
theorem halfSpinLinearIsometryEquiv_comp_halfSpinCliffordMul {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ) (v : V) :
    (halfSpinLinearIsometryEquiv o' ho hU (-ε)).toLinearEquiv.toLinearMap ∘ₗ
        halfSpinCliffordMul o ρ ε v =
      halfSpinCliffordMul o' ρ' ε (f v) ∘ₗ
        (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap := by
  ext ψ
  simpa using LinearMap.congr_fun (hU v) ψ

/-- The unitary half-spin restriction intertwines `evenHalfSpinAction` along the even Clifford
homomorphism of any quadratic isometry `e : Q →qᵢ Q'` agreeing with `f`. -/
theorem halfSpinLinearIsometryEquiv_comp_evenHalfSpinAction {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap)
    (e : Q →qᵢ Q') (he : ∀ v, e v = f v) (ε : ℂ) (x : even Q) :
    (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap ∘ₗ
        evenHalfSpinAction o ρ ε x =
      evenHalfSpinAction o' ρ' ε ⟨CliffordAlgebra.map e x, map_mem_even e x.2⟩ ∘ₗ
        (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap := by
  have hx := comp_eq_map_comp_of_forall_ι (f := e)
    (fun v ↦ by simpa [he v] using hU v) (x : CliffordAlgebra Q)
  ext ψ
  simpa using LinearMap.congr_fun hx ψ

/-- **Canonical transport of operators between chirality eigenspaces**: when `complexifyAction ρ`
is surjective on a nontrivial module `W` (in particular whenever `dim_ℂ W⁺ = 2`), conjugating any
linear map `T : W^{ε₁} →ₗ[ℂ] W^{ε₂}` by `halfSpinLinearIsometryEquiv` is independent of the choice
of unitary Clifford intertwiner `U` along `(f, ho)`. -/
theorem conj_halfSpinLinearIsometryEquiv_eq [Nontrivial W]
    (hsurj : Function.Surjective (complexifyAction ρ))
    {U₁ U₂ : W ≃ₗᵢ[ℂ] W'}
    (hU₁ : ∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap)
    (hU₂ : ∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap)
    {ε₁ ε₂ : ℂ}
    (T : eigenspace (ρ (chirality Q o)) ε₁ →ₗ[ℂ] eigenspace (ρ (chirality Q o)) ε₂) :
    (halfSpinLinearIsometryEquiv o' ho hU₂ ε₂).toLinearEquiv.toLinearMap ∘ₗ
        T ∘ₗ (halfSpinLinearIsometryEquiv o' ho hU₂ ε₁).symm.toLinearEquiv.toLinearMap =
      (halfSpinLinearIsometryEquiv o' ho hU₁ ε₂).toLinearEquiv.toLinearMap ∘ₗ
        T ∘ₗ (halfSpinLinearIsometryEquiv o' ho hU₁ ε₁).symm.toLinearEquiv.toLinearMap := by
  obtain ⟨z, hz, _⟩ := existsUnique_circle_smul_intertwiner hsurj U₁ U₂ hU₁ hU₂
  have hsymm (w' : W') : U₂.symm w' = (z⁻¹ : Circle) • U₁.symm w' := by
    apply U₂.injective
    rw [U₂.apply_symm_apply, Circle.smul_def, map_smul, hz, smul_smul, ← Circle.coe_mul,
      inv_mul_cancel, Circle.coe_one, one_smul, U₁.apply_symm_apply]
  ext ψ'
  have h₁ : (halfSpinLinearIsometryEquiv o' ho hU₂ ε₁).symm ψ' =
      ((z : ℂ)⁻¹) • (halfSpinLinearIsometryEquiv o' ho hU₁ ε₁).symm ψ' := by
    apply Subtype.ext
    simpa [Circle.smul_def] using hsymm ψ'
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [h₁, map_smul, map_smul, Submodule.coe_smul, coe_halfSpinLinearIsometryEquiv_apply,
    coe_halfSpinLinearIsometryEquiv_apply, hz, smul_smul, inv_mul_cancel₀ z.coe_ne_zero, one_smul]

end HalfSpinIntertwiner

end DimensionFour

end CliffordAlgebra
