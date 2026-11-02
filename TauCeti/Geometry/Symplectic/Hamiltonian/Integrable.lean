/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Open
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.StandardCompatible

import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.RegularValue.Factorization

/-!
# First integrals and completely integrable systems

Let `σ` be a nondegenerate two-form on a manifold `M`, with the conventions `ι_{X_f} σ = df` and
`{f, g} = σ(X_f, X_g) = df(X_g)`. A function `g` is a **first integral** of a Hamiltonian `f`
when `{g, f} = 0` (`TauCeti.SmoothTwoForm.IsFirstIntegral`), that is when `g` is stationary along
the Hamiltonian vector field `X_f`. When `σ` is nondegenerate and `M` is finite-dimensional, a
first integral which is differentiable at every point of an integral curve of `X_f` is constant
along that curve (`TauCeti.SmoothTwoForm.IsFirstIntegral.apply_eq_of_isMIntegralCurve`). Being a
first integral is a symmetric relation, by antisymmetry of the Poisson bracket.

A **completely integrable system** on a `2n`-dimensional manifold is a smooth map
`F : M → (ι → ℝ)` with `n` components `F_i`, pairwise in involution, `{F_i, F_j} = 0`, whose
differentials `dF_i` are independent on a dense set of points
(`TauCeti.SmoothTwoForm.IsIntegrableSystem`). Independence at `x` means that `dF_x : T_x M → ℝⁿ`
is surjective, that is `x` is a regular point of `F`. The regular points form an open set, so they
form a dense open set (`TauCeti.SmoothTwoForm.IsIntegrableSystem.isOpen_setOf_isRegularPoint`).

At a regular point `x`, the kernel of `dF_x`, the tangent space of the common level of the `F_i`,
is Lagrangian (`TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangian_ker_mfderiv`). A function
`f` Poisson-commutes at `x` with every `F_i` exactly when its differential vanishes on this
kernel (`TauCeti.SmoothTwoForm.IsIntegrableSystem.ker_mfderiv_le_ker_iff`): a Hamiltonian belongs
to the system exactly when, at regular points, its differential is a combination of the `dF_i`.
Such a function is then locally a function of the integrals: near a regular point `x`, a `C^n`
function `f` Poisson-commuting with every `F_i` is `ψ ∘ F` with `ψ` of class `C^n` at `F x`
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_eventuallyEq_comp`). On an open set of regular
points whose fibres under `F` are connected, it is a single such function of `F`
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_eqOn_comp`); on disconnected fibres it may take
different values on different components.

Integrability does not depend on coordinates: it is preserved by pulling back along a local
diffeomorphism which pulls the form back to the form, such as a symplectomorphism
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.comp_isLocalDiffeomorph`), and by reparametrizing the
values of `F` by a smooth map with surjective derivatives between spaces of the same dimension
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.comp_left`).

The energy `(q² + p²) / 2` of the harmonic oscillator on the plane is an integrable system with a
single critical point (`TauCeti.isIntegrableSystem_harmonicOscillator`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsFirstIntegral σ f g`: `g` is a first integral of the Hamiltonian `f`.
* `TauCeti.SmoothTwoForm.IsIntegrableSystem σ F`: `F` is a completely integrable system.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 40 and 49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

open Function Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {f g k : M → ℝ}

/-! ### First integrals -/

/-- A function `g` is a **first integral** of the Hamiltonian `f` when the Poisson bracket
`{g, f}` vanishes everywhere. For a nondegenerate form on a finite-dimensional manifold this says
that `g` is stationary along the Hamiltonian vector field of `f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isFirstIntegral_iff_mvfderiv`), so that `g` is constant
along every integral curve of the Hamiltonian vector field of `f` on which `g` is differentiable
(`TauCeti.SmoothTwoForm.IsFirstIntegral.apply_eq_of_isMIntegralCurveOn`). -/
def IsFirstIntegral (σ : SmoothTwoForm I M) (f g : M → ℝ) : Prop :=
  ∀ x, σ.poissonBracket g f x = 0

theorem isFirstIntegral_iff : σ.IsFirstIntegral f g ↔ ∀ x, σ.poissonBracket g f x = 0 :=
  Iff.rfl

/-- Being a first integral is symmetric: `g` is a first integral of `f` exactly when `f` is a
first integral of `g`. -/
theorem isFirstIntegral_comm : σ.IsFirstIntegral f g ↔ σ.IsFirstIntegral g f := by
  simp only [isFirstIntegral_iff, ← neg_poissonBracket σ g f, neg_eq_zero]

alias ⟨IsFirstIntegral.symm, _⟩ := isFirstIntegral_comm

/-- A Hamiltonian is a first integral of itself. -/
@[simp]
theorem isFirstIntegral_self (f : M → ℝ) : σ.IsFirstIntegral f f :=
  fun x ↦ poissonBracket_self σ f x

/-- A constant function is a first integral of every Hamiltonian. -/
@[simp]
theorem isFirstIntegral_const (f : M → ℝ) (c : ℝ) : σ.IsFirstIntegral f fun _ ↦ c :=
  fun x ↦ poissonBracket_const_left σ c f x

/-- A sum of differentiable first integrals is a first integral. -/
theorem IsFirstIntegral.add (hg : σ.IsFirstIntegral f g) (hk : σ.IsFirstIntegral f k)
    (hg' : MDifferentiable I 𝓘(ℝ) g) (hk' : MDifferentiable I 𝓘(ℝ) k) :
    σ.IsFirstIntegral f (g + k) := fun x ↦ by
  rw [poissonBracket_add_left (hg' x) (hk' x), hg x, hk x, add_zero]

/-- The negative of a first integral is a first integral. -/
theorem IsFirstIntegral.neg (hg : σ.IsFirstIntegral f g) : σ.IsFirstIntegral f (-g) := fun x ↦ by
  rw [poissonBracket_neg_left, hg x, neg_zero]

/-- A constant multiple of a first integral is a first integral. -/
theorem IsFirstIntegral.const_smul (hg : σ.IsFirstIntegral f g) (c : ℝ) :
    σ.IsFirstIntegral f (c • g) := fun x ↦ by
  rw [poissonBracket_const_smul_left, hg x, smul_zero]

section Nondegenerate

variable [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
include hσ

/-- A first integral of `f` is a function stationary along the Hamiltonian vector field of `f`. -/
theorem IsNondegenerate.isFirstIntegral_iff_mvfderiv :
    σ.IsFirstIntegral f g ↔ ∀ x, mvfderiv I g x (σ.hamiltonianVectorField f x) = 0 := by
  simp only [isFirstIntegral_iff, hσ.poissonBracket_eq_mvfderiv]

/-- **Conservation of first integrals.** A first integral `g` of `f`, differentiable along an
integral curve of the Hamiltonian vector field of `f` on an open interval of times (or any open
preconnected set of times), is constant along that curve. -/
theorem IsFirstIntegral.apply_eq_of_isMIntegralCurveOn (hg : σ.IsFirstIntegral f g) {γ : ℝ → M}
    {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ (σ.hamiltonianVectorField f) s)
    (hgγ : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) g (γ t)) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    g (γ t) = g (γ t₀) :=
  hγ.apply_eq_of_mvfderiv_apply_eq_zero hs hs' hgγ
    (fun u _ ↦ hσ.isFirstIntegral_iff_mvfderiv.1 hg (γ u)) ht₀ ht

/-- **Conservation of first integrals** along a global integral curve: a first integral of `f`,
differentiable along an integral curve of the Hamiltonian vector field of `f`, is constant along
that curve. -/
theorem IsFirstIntegral.apply_eq_of_isMIntegralCurve (hg : σ.IsFirstIntegral f g) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField f))
    (hgγ : ∀ t, MDifferentiableAt I 𝓘(ℝ) g (γ t)) (s t : ℝ) :
    g (γ t) = g (γ s) :=
  hg.apply_eq_of_isMIntegralCurveOn hσ isOpen_univ isPreconnected_univ (hγ.isMIntegralCurveOn _)
    (fun t _ ↦ hgγ t) (Set.mem_univ s) (Set.mem_univ t)

end Nondegenerate

/-! ### Completely integrable systems -/

variable {ι : Type*} [Fintype ι] {F : M → ι → ℝ} {x : M}

/-- A smooth map `F : M → (ι → ℝ)` is a **completely integrable system** for the two-form `σ` on
a manifold of dimension twice the number of components of `F`, when the components `F_i`
Poisson-commute pairwise and their differentials are independent on a dense set: the regular
points of `F`, at which `dF_x` is surjective, are dense. They then form a dense open set
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.isOpen_setOf_isRegularPoint`). The definition is
meant for a nondegenerate form; the results about it assume nondegeneracy. -/
structure IsIntegrableSystem [FiniteDimensional ℝ E] (σ : SmoothTwoForm I M) (F : M → ι → ℝ) :
    Prop where
  /-- The integrals of an integrable system are smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F
  /-- The integrals of an integrable system Poisson-commute pairwise. -/
  poissonBracket_eq_zero : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0
  /-- The integrals of an integrable system have independent differentials on a dense set. -/
  dense_setOf_isRegularPoint : Dense {x | IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x}
  /-- An integrable system has half as many integrals as the dimension of the manifold. -/
  two_mul_card_eq_finrank : 2 * Fintype.card ι = finrank ℝ E

namespace IsIntegrableSystem

variable [FiniteDimensional ℝ E] (h : σ.IsIntegrableSystem F)
include h

/-- Each integral of an integrable system is a first integral of every other. -/
theorem isFirstIntegral (i j : ι) : σ.IsFirstIntegral (F · i) (F · j) :=
  h.poissonBracket_eq_zero j i

/-- **The regular points of an integrable system form an open set**, which is dense by
definition. -/
theorem isOpen_setOf_isRegularPoint : IsOpen {x | IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x} :=
  TauCeti.isOpen_setOf_isRegularPoint h.contMDiff (by simp)

variable (hσ : σ.IsNondegenerate)
include hσ

/-- **Regular common levels of an integrable system are Lagrangian.** At a regular point `x` the
kernel of `dF_x` is a Lagrangian subspace of `T_x M`. -/
theorem isLagrangian_ker_mfderiv (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    (hσ.symplecticFormAt x).IsLagrangian (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker :=
  (hσ.isLagrangian_ker_mfderiv_iff hx (h.poissonBracket_eq_zero · · x)).2
    h.two_mul_card_eq_finrank

/-- **The functions in involution with an integrable system.** At a regular point `x`, a function
`f` Poisson-commutes with every integral `F_i` exactly when its differential vanishes on the
kernel of `dF_x`, that is when `df_x` is a linear combination of the `dF_i`. -/
theorem ker_mfderiv_le_ker_iff (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (f : M → ℝ) :
    (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ≤ (mvfderiv I f x).ker ↔
      ∀ i, σ.poissonBracket (F · i) f x = 0 := by
  rw [hσ.ker_mfderiv_eq_span_hamiltonianVectorField hx (h.poissonBracket_eq_zero · · x)
    h.two_mul_card_eq_finrank, Submodule.span_le, Set.range_subset_iff]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    hσ.poissonBracket_eq_neg_mvfderiv, neg_eq_zero]

/-- A Hamiltonian `f` of which every integral `F_i` is a first integral has, at each regular
point `x`, a differential vanishing on the kernel of `dF_x`. -/
theorem ker_mfderiv_le_ker_of_isFirstIntegral (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hf : ∀ i, σ.IsFirstIntegral f (F · i)) :
    (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ≤ (mvfderiv I f x).ker :=
  (h.ker_mfderiv_le_ker_iff hσ hx f).2 fun i ↦ hf i x

section Boundaryless

variable [I.Boundaryless] {n : ℕ∞ω}

/-- **Functions in involution with an integrable system are locally functions of its
integrals.** On a boundaryless manifold, let `x` be a regular point of an integrable system `F`,
and let `f` be `C^n` at `x`, with `0 < n ≤ ∞`. If near `x` the function `f` Poisson-commutes with
every integral `F_i`, then near `x` it is `ψ ∘ F` for a function `ψ` of the values of the
integrals which is `C^n` at `F x`. -/
theorem exists_eventuallyEq_comp (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (hn : n ≠ 0)
    (hn' : n ≤ ∞) (hf : ContMDiffAt I 𝓘(ℝ) n f x)
    (hfF : ∀ᶠ y in 𝓝 x, ∀ i, σ.poissonBracket (F · i) f y = 0) :
    ∃ ψ : (ι → ℝ) → ℝ, ContDiffAt ℝ n ψ (F x) ∧ f =ᶠ[𝓝 x] ψ ∘ F := by
  refine hx.exists_eventuallyEq_comp_of_ker_mfderiv_le ((h.contMDiff x).of_le hn') hf hn ?_
  filter_upwards [h.isOpen_setOf_isRegularPoint.mem_nhds hx, hfF] with y hy hyf
  intro v hv
  exact (mvfderiv_apply_eq_mfderiv_apply f y v).symm.trans
    (LinearMap.mem_ker.1 ((h.ker_mfderiv_le_ker_iff hσ hy f).2 hyf hv))

/-- **Functions in involution with an integrable system are functions of its integrals on sets
with connected fibres.** On a boundaryless manifold, let `U` be an open set of regular points of
an integrable system `F` such that each fibre `U ∩ F ⁻¹' {c}` is preconnected, and let `f` be
`C^n` on `U`, with `0 < n ≤ ∞`. If `f` Poisson-commutes on `U` with every integral `F_i`, then on
`U` it is `ψ ∘ F` for a single function `ψ` which is `C^n` at every value of `F` on `U`. -/
theorem exists_eqOn_comp {U : Set M} (hU : IsOpen U)
    (hreg : ∀ y ∈ U, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) (hn : n ≠ 0) (hn' : n ≤ ∞)
    (hf : ContMDiffOn I 𝓘(ℝ) n f U)
    (hfF : ∀ y ∈ U, ∀ i, σ.poissonBracket (F · i) f y = 0)
    (hconn : ∀ c, IsPreconnected (U ∩ F ⁻¹' {c})) :
    ∃ ψ : (ι → ℝ) → ℝ, Set.EqOn f (ψ ∘ F) U ∧ ∀ y ∈ U, ContDiffAt ℝ n ψ (F y) :=
  exists_eqOn_comp_of_ker_mfderiv_le hU hreg ((h.contMDiff.of_le hn').contMDiffOn) hf hn
    (fun y hy v hv ↦ (mvfderiv_apply_eq_mfderiv_apply f y v).symm.trans
      (LinearMap.mem_ker.1 ((h.ker_mfderiv_le_ker_iff hσ (hreg y hy) f).2 (hfF y hy) hv))) hconn

end Boundaryless

end IsIntegrableSystem

/-! ### Invariance of integrability -/

namespace IsIntegrableSystem

variable [FiniteDimensional ℝ E]

section LocalDiffeomorph

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂]
  [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂} {G : M₂ → ι → ℝ}
  {φ : M → M₂}

/-- **Integrable systems are invariant under canonical transformations.** Let `φ` be a local
diffeomorphism, such as a symplectomorphism, pulling a nondegenerate form `σ₂` back to `σ`. Then
`G ∘ φ` is an integrable system for `σ` whenever `G` is one for `σ₂`. The manifold `M` is assumed
nonempty, so that `φ` relates the dimensions of the two manifolds. -/
theorem comp_isLocalDiffeomorph [Nonempty M] (h : σ₂.IsIntegrableSystem G)
    (hσ₂ : σ₂.IsNondegenerate) (hφ : IsLocalDiffeomorph I I₂ ∞ φ)
    (hφσ : SmoothForm.mpullback φ hφ.contMDiff σ₂ = σ) : σ.IsIntegrableSystem (G ∘ φ) where
  contMDiff := h.contMDiff.comp hφ.contMDiff
  poissonBracket_eq_zero i j x := by
    have hinv := hφ.isInvertible_mfderiv (by simp)
    -- `σ = φ^* σ₂` is nondegenerate, since `φ` has invertible differentials.
    have hσ : σ.IsNondegenerate := hφσ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph hφ
    have hG (l : ι) : MDifferentiableAt I₂ 𝓘(ℝ) (G · l) (φ x) :=
      (((ContinuousLinearMap.proj l : (ι → ℝ) →L[ℝ] ℝ).contMDiff.comp h.contMDiff)
        (φ x)).mdifferentiableAt (by simp)
    exact (hσ.poissonBracket_comp hσ₂ hφ.contMDiff hφσ (hinv x).surjective (hG i) (hG j)).trans
      (h.poissonBracket_eq_zero i j (φ x))
  dense_setOf_isRegularPoint := by
    -- A point is regular for `G ∘ φ` exactly when its image is regular for `G`.
    have hreg : {x | IsRegularPoint I 𝓘(ℝ, ι → ℝ) (G ∘ φ) x} =
        φ ⁻¹' {y | IsRegularPoint I₂ 𝓘(ℝ, ι → ℝ) G y} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, isRegularPoint_iff,
        mfderiv_comp x ((h.contMDiff (φ x)).mdifferentiableAt (by simp))
          (hφ.mdifferentiable (by simp) x), ContinuousLinearMap.coe_comp]
      exact ⟨fun hs ↦ hs.of_comp, fun hs ↦ hs.comp (hφ.isInvertible_mfderiv (by simp) x).surjective⟩
    rw [hreg]
    exact h.dense_setOf_isRegularPoint.preimage hφ.isOpenMap
  two_mul_card_eq_finrank := by
    rw [h.two_mul_card_eq_finrank]
    exact ((hφ.mfderivToContinuousLinearEquiv (by simp)
      (Classical.arbitrary M)).toLinearEquiv.finrank_eq).symm

end LocalDiffeomorph

variable {κ : Type*} [Fintype κ] {ψ : (ι → ℝ) → κ → ℝ} {U : Set (ι → ℝ)}

/-- **Integrable systems are invariant under reparametrization.** If `ψ` is smooth on an open set
`U` containing the values of an integrable system `F`, with surjective derivatives at these values,
between spaces of the same dimension, then `ψ ∘ F` is an integrable system. -/
theorem comp_left (h : σ.IsIntegrableSystem F) (hσ : σ.IsNondegenerate) (hU : IsOpen U)
    (hFU : ∀ x, F x ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψF : ∀ x, Surjective (fderiv ℝ ψ (F x))) (hκ : Fintype.card κ = Fintype.card ι) :
    σ.IsIntegrableSystem (ψ ∘ F) where
  contMDiff := (contMDiffOn_iff_contDiffOn.2 hψ).comp_contMDiff h.contMDiff hFU
  poissonBracket_eq_zero a b x := by
    have hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x := (h.contMDiff x).mdifferentiableAt (by simp)
    have hψx : DifferentiableAt ℝ ψ (F x) :=
      ((hψ.contDiffAt (hU.mem_nhds (hFU x))).differentiableAt (by simp))
    -- The differential of each component `ψ_c ∘ F` factors through `dF_x`.
    have hker (c : κ) : (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ≤ (mvfderiv I ((ψ ∘ F) · c) x).ker := by
      intro v hv
      have hψc : DifferentiableAt ℝ (fun z ↦ ψ z c) (F x) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ↦ ℝ) c).differentiableAt.comp _ hψx
      rw [LinearMap.mem_ker] at hv ⊢
      rw [ContinuousLinearMap.coe_coe] at hv ⊢
      refine (mvfderiv_comp_apply_of_differentiableAt hψc hF v).trans ?_
      rw [mvfderiv_apply_eq_mfderiv_apply, hv]
      exact (fderiv ℝ (fun z ↦ ψ z c) (F x)).map_zero
    exact hσ.poissonBracket_eq_zero_of_ker_le hF (h.poissonBracket_eq_zero · · x) (hker a)
      (hker b)
  dense_setOf_isRegularPoint := by
    refine h.dense_setOf_isRegularPoint.mono fun x hx ↦ ?_
    have hψx : DifferentiableAt ℝ ψ (F x) :=
      ((hψ.contDiffAt (hU.mem_nhds (hFU x))).differentiableAt (by simp))
    rw [Set.mem_ofPred_eq] at hx
    rw [Set.mem_ofPred_eq, isRegularPoint_iff, mfderiv_comp x hψx.mdifferentiableAt
      (h.contMDiff x |>.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    refine Surjective.comp ?_ (isRegularPoint_iff.1 hx)
    rw [mfderiv_eq_fderiv]
    exact hψF x
  two_mul_card_eq_finrank := hκ ▸ h.two_mul_card_eq_finrank

end IsIntegrableSystem

end SmoothTwoForm

/-! ### Example: the harmonic oscillator -/

/-- **The harmonic oscillator is completely integrable.** On the plane `ℝ × ℝ` with its standard
symplectic form, the energy `(q² + p²) / 2` of the harmonic oscillator is an integrable system
with one integral. Its only critical point is the origin, so its regular points are dense. -/
theorem isIntegrableSystem_harmonicOscillator :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsIntegrableSystem
      fun z : ℝ × ℝ ↦ fun _ : Fin 1 ↦ (z.1 ^ 2 + z.2 ^ 2) / 2 where
  contMDiff := contMDiff_iff_contDiff.2 (contDiff_pi.2 fun _ ↦ by fun_prop)
  -- With a single integral, involutivity is the vanishing of `{F₀, F₀}`.
  poissonBracket_eq_zero _ _ x := SmoothTwoForm.poissonBracket_self _ _ x
  dense_setOf_isRegularPoint := by
    refine (dense_compl_singleton (0 : ℝ × ℝ)).mono fun z hz ↦ ?_
    rw [Set.mem_compl_singleton_iff] at hz
    set r := z.1 ^ 2 + z.2 ^ 2
    have hr : r ≠ 0 := by
      intro h0
      apply hz
      ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    -- The derivative at `z = (q, p)` is `v ↦ q v₁ + p v₂`, which takes the value `w` at the
    -- multiple `(w / r) • z` of `z`.
    let L : ℝ × ℝ →L[ℝ] Fin 1 → ℝ :=
      ContinuousLinearMap.pi fun _ ↦ z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
    have hL : HasFDerivAt (fun z : ℝ × ℝ ↦ fun _ : Fin 1 ↦ (z.1 ^ 2 + z.2 ^ 2) / 2) L z := by
      refine hasFDerivAt_pi.2 fun _ ↦ ?_
      have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)).pow 2
      have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)).pow 2
      simp only [div_eq_mul_inv]
      convert (h1.add h2).mul_const (2⁻¹ : ℝ) using 1
      ext <;> simp
    rw [Set.mem_ofPred_eq, isRegularPoint_iff_surjective_fderiv, hL.fderiv]
    intro w
    refine ⟨(w 0 / r) • z, funext fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]
    simp only [L, ContinuousLinearMap.pi_apply, add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    field_simp
    ring
  two_mul_card_eq_finrank := by simp

/-- **The energy of the harmonic oscillator is proper.** The map `(q, p) ↦ (q² + p²) / 2` on the
plane, the integrable system of `TauCeti.isIntegrableSystem_harmonicOscillator`, is a proper map:
it grows like the square of the norm. -/
theorem isProperMap_harmonicOscillator :
    IsProperMap fun z : ℝ × ℝ ↦ fun _ : Fin 1 ↦ (z.1 ^ 2 + z.2 ^ 2) / 2 := by
  refine isProperMap_iff_tendsto_cocompact.2 ⟨by fun_prop, ?_⟩
  rw [← Metric.cobounded_eq_cocompact (α := Fin 1 → ℝ), ← tendsto_norm_atTop_iff_cobounded]
  refine Filter.tendsto_atTop_mono (fun z ↦ ?_)
    (((Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).atTop_div_const
      two_pos)
  -- The sup norm satisfies `‖z‖² = max (q², p²) ≤ q² + p²`.
  rw [Function.comp_apply, pi_norm_const, Real.norm_of_nonneg (by positivity), Prod.norm_def]
  gcongr
  rcases max_cases ‖z.1‖ ‖z.2‖ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h, Real.norm_eq_abs, sq_abs] <;>
    nlinarith [sq_nonneg z.1, sq_nonneg z.2]

end TauCeti
