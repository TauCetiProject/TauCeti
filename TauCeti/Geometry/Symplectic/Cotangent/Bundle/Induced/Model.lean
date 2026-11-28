/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.Nondegenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The Marle–Guillemin–Sternberg local model

Let a Hamiltonian action of a Lie group `G` have a point `p` with stabilizer `K` and moment value
`ν`. Near the orbit of `p` the action is modelled by the balanced product

`Y = G ×_K (𝔪* × V)`,  `k • (g, a, v) = (g k⁻¹, k • a, k • v)`,

where `V` is the symplectic slice at `p`, a symplectic representation of `K`, and `𝔪` is a
`K`-invariant complement of the Lie algebra `𝔨` of `K` in the Lie algebra `𝔤_ν` of the coadjoint
stabilizer of `ν`. This file instantiates the symplectic induction of
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct` on this model, for linear
data:

* a symplectic vector space `(V, ω)` on which `K` acts smoothly by linear symplectomorphisms, with
  its quadratic moment map `μ_V(v)(κ) = ½ ω(κ_V v, v)`
  (`TauCeti.SymplecticForm.linearActionMomentMap`);
* a smooth linear action of `K` on `𝔪*`, a continuous linear map `P : 𝔤 → 𝔪` vanishing on `𝔨`
  with `(k • a) ∘ P = Ad*_k (a ∘ P)`, and a continuous linear map `R : 𝔤 → 𝔨` restricting to the
  identity of `𝔨` and intertwining the adjoint actions; for invariant splittings
  `𝔤 = 𝔨 ⊕ 𝔪 ⊕ 𝔮`, these are the projections onto `𝔪` and onto `𝔨`;
* a covector `ν ∈ 𝔤*` fixed by the coadjoint action of `K`.

The fibre `𝔪* × V` carries the closed two-form `pr_V^* ω` (`TauCeti.CotangentBundle.localModelForm`)
and the map

`f(a, v) = ν + a ∘ P + μ_V(v) ∘ R`

(`TauCeti.CotangentBundle.localModelMap`). It is smooth
(`TauCeti.CotangentBundle.contDiff_localModelMap`) and `K`-equivariant,
`f(k • (a, v)) = Ad*_k f(a, v)` (`TauCeti.CotangentBundle.localModelMap_smul`); the form is
`K`-invariant (`TauCeti.CotangentBundle.mpullback_smul_localModelForm`); and the restriction of `f`
to `𝔨` is the moment map `ν|_𝔨 + μ_V` of the action of `K`
(`TauCeti.CotangentBundle.isMomentMap_localModelForm`). These are the hypotheses of the descent,
so the induced form `Ω = -d⟨f, θ⟩ + pr^* ω` descends to a closed two-form on `Y`, with the
coadjoint-equivariant moment map `[g, a, v] ↦ Ad*_g (ν + a ∘ P + μ_V(v) ∘ R)` for the left action
of `G` (`TauCeti.CotangentBundle.balancedProductInducedForm`,
`TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductInducedForm`), equal to `Ad*_g ν` on
the zero orbit (`TauCeti.CotangentBundle.balancedProductInducedMomentMap_localModelMap_mk_zero`).

**The form at the base point.** The quadratic moment map `μ_V` has zero derivative at the origin,
so `df` at `(0, 0)` is `(a, v) ↦ a ∘ P`
(`TauCeti.CotangentBundle.fderiv_localModelMap_zero`), and at `[1, 0, 0]` the descended form is

`Ω((ξ, a, u), (ζ, b, w)) = b(P ξ) - a(P ζ) + ν ⁅ξ, ζ⁆ + ω(u, w)`

(`TauCeti.CotangentBundle.eval₂_balancedProductInducedForm_localModelForm_mfderiv_one_zero`): the
pairing of `𝔪` with `𝔪*`, the Kirillov–Kostant–Souriau tensor of `ν`, which only sees the
components in a complement of `𝔤_ν`, and the slice form.

**Nondegeneracy near the zero orbit.** If `P` maps `𝔤_ν` onto `𝔪` and `𝔤_ν ∩ ker P ⊆ 𝔨`, that is
`𝔤_ν = 𝔨 ⊕ 𝔪`, the descended form is nondegenerate at every point `[g, 0, 0]` of the zero orbit
(`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm_mk`),
hence on an open `G`-invariant neighbourhood of it
(`exists_isOpen_nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm`, in the
namespace `TauCeti.CotangentBundle`), on which `Y` is a Hamiltonian `G`-manifold. No properness or
compactness is used here: they enter when the model is compared with a neighbourhood of an actual
orbit.

## Main definitions

All declarations are in the namespace `TauCeti.CotangentBundle`.

* `localModelMap`: the map `f(a, v) = ν + a ∘ P + μ_V(v) ∘ R`.
* `localModelForm`: the fibre form `pr_V^* ω` on `𝔪* × V`.

## Main results

* `localModelMap_smul`, `mpullback_smul_localModelForm`, `isMomentMap_localModelForm`: the
  hypotheses of symplectic induction.
* `eval₂_balancedProductInducedForm_localModelForm_mfderiv_one_zero`: the model tensor at the base
  point.
* `nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm_mk`,
  `exists_isOpen_nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm`:
  nondegeneracy along the zero orbit and on an invariant neighbourhood of it.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2 (the local model `G ×_H (𝔪* × V)`, its form and its moment map).
-/

public section

noncomputable section

open Function Manifold TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] {K : Subgroup G}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F K]
  {𝔪 : Type*} [NormedAddCommGroup 𝔪] [NormedSpace ℝ 𝔪]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [DistribMulAction K V] [SMulCommClass K ℝ V] [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, V) ∞ K V]
  (ωV : SymplecticForm V)

/-! ### The map `f (a, v) = ν + a ∘ P + μ_V(v) ∘ R` -/

variable (ν : E →L[ℝ] ℝ) (P : E →L[ℝ] 𝔪) (R : E →L[ℝ] GroupLieAlgebra 𝓘(ℝ, F) K)

/-- The moment map of the fibre of the local model `G ×_K (𝔪* × V)`,
`f (a, v) = ν + a ∘ P + μ_V(v) ∘ R`, where `μ_V(v)(κ) = ½ ω(κ_V v, v)` is the quadratic moment map
of the linear action of `K` on `(V, ω)` (`TauCeti.SymplecticForm.linearActionMomentMap`). -/
def localModelMap (p : StrongDual ℝ 𝔪 × V) : E →L[ℝ] ℝ :=
  ν + p.1.comp P + LinearMap.toContinuousLinearMap
    ((SymplecticForm.linearActionMomentMap 𝓘(ℝ, F) K ωV p.2).comp R.toLinearMap)

omit [FiniteDimensional ℝ V] in
/-- The fibre moment map of the local model evaluated at `ξ ∈ 𝔤`. -/
@[simp]
theorem localModelMap_apply (p : StrongDual ℝ 𝔪 × V) (ξ : E) :
    localModelMap ωV ν P R p ξ =
      ν ξ + p.1 (P ξ) + SymplecticForm.linearActionMomentMap 𝓘(ℝ, F) K ωV p.2 (R ξ) :=
  (rfl)

/-- The fibre moment map of the local model is smooth: it is the sum of a constant, a continuous
linear map and a continuous quadratic map. -/
theorem contDiff_localModelMap : ContDiff ℝ ∞ (localModelMap ωV ν P R) := by
  refine (contDiff_const.add (contDiff_fst.clm_comp contDiff_const)).add
    (contDiff_clm_apply_iff.2 fun ξ ↦ ?_)
  -- The component at `ξ` is `p ↦ ω(L p.2, p.2) / 2` for the linear map `L = (R ξ)_V`.
  set L : V →L[ℝ] V := LinearMap.toContinuousLinearMap
    (fundamentalLinearMap 𝓘(ℝ, F) K V (R ξ))
  have hB := ωV.toBilinForm.toContinuousBilinearMap.isBoundedBilinearMap.contDiff (n := ∞)
  have h := (hB.comp ((L.contDiff.comp (contDiff_snd (E := StrongDual ℝ 𝔪) (F := V))).prodMk
    (contDiff_snd (E := StrongDual ℝ 𝔪) (F := V)))).div_const 2
  convert h using 1
  funext p
  simp [L]

omit [FiniteDimensional ℝ V] in
/-- At the base point `(0, 0)` the fibre moment map of the local model is `ν`. -/
@[simp]
theorem localModelMap_zero : localModelMap ωV ν P R 0 = ν := by
  ext ξ
  simp [localModelMap_apply]

omit [FiniteDimensional ℝ V] in
/-- Along the line through `u = (a, v)`, `f (t u) = ν + t (a ∘ P) + t² μ_V(v) ∘ R`. -/
private theorem localModelMap_real_smul (t : ℝ) (u : StrongDual ℝ 𝔪 × V) :
    localModelMap ωV ν P R (t • u) =
      ν + t • u.1.comp P + (t ^ 2) • (localModelMap ωV ν P R u - ν - u.1.comp P) := by
  ext ξ
  simp only [localModelMap_apply, Prod.smul_fst, Prod.smul_snd, add_apply,
    smul_apply, sub_apply, ContinuousLinearMap.comp_apply,
    SymplecticForm.linearActionMomentMap_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The derivative of the fibre moment map at the base point** is `(a, v) ↦ a ∘ P`: the
quadratic slice moment map has zero derivative at the origin. -/
theorem fderiv_localModelMap_zero (u : StrongDual ℝ 𝔪 × V) :
    fderiv ℝ (localModelMap ωV ν P R) 0 u = u.1.comp P := by
  -- Differentiate `t ↦ f (t u)` at `0` in two ways: by the chain rule, and from its expression
  -- as a polynomial in `t`.
  have hchain := ((contDiff_localModelMap ωV ν P R).differentiable (by simp) 0).hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const u) (zero_smul ℝ u).symm
  have hpoly : HasDerivAt (fun t : ℝ ↦ localModelMap ωV ν P R (t • u)) (u.1.comp P) 0 := by
    simp_rw [localModelMap_real_smul]
    exact (((hasDerivAt_const (0 : ℝ) ν).add ((hasDerivAt_id (0 : ℝ)).smul_const
      (u.1.comp P))).add ((hasDerivAt_pow 2 (0 : ℝ)).smul_const
        (localModelMap ωV ν P R u - ν - u.1.comp P))).congr_deriv (by simp)
  simpa using hchain.unique hpoly

/-- The derivative of the fibre moment map at the base point, read as a manifold derivative:
`df_0(a, v) = a ∘ P`. -/
theorem mvfderiv_localModelMap_zero (u : TangentSpace 𝓘(ℝ, StrongDual ℝ 𝔪 × V) 0) :
    mvfderiv 𝓘(ℝ, StrongDual ℝ 𝔪 × V) (localModelMap ωV ν P R) 0 u = u.1.comp P := by
  rw [mvfderiv_eq_fderiv_apply]
  exact fderiv_localModelMap_zero ωV ν P R u

/-! ### The fibre form `pr_V^* ω` -/

variable (𝔪) in
/-- The two-form `pr_V^* ω` on the fibre `𝔪* × V` of the local model `G ×_K (𝔪* × V)`: it pairs
`(a, u)` and `(b, w)` to `ω(u, w)` (`TauCeti.CotangentBundle.eval₂_localModelForm`). -/
def localModelForm : SmoothTwoForm 𝓘(ℝ, StrongDual ℝ 𝔪 × V) (StrongDual ℝ 𝔪 × V) :=
  SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff ωV.constSmooth

/-- The fibre form of the local model pairs `(a, u)` and `(b, w)` to `ω(u, w)`. -/
theorem eval₂_localModelForm (p : StrongDual ℝ 𝔪 × V)
    (u w : TangentSpace 𝓘(ℝ, StrongDual ℝ 𝔪 × V) p) :
    (localModelForm 𝔪 ωV).eval₂ p u w = ωV u.2 w.2 := by
  rw [localModelForm, SmoothForm.eval₂_mpullback, ωV.eval₂_constSmooth_mfderiv_eq,
    mvfderiv_eq_fderiv_apply, mvfderiv_eq_fderiv_apply, fderiv_snd]
  -- `snd u` is `u.2`, read through the identification of the tangent space with the model.
  rfl

/-- The fibre form of the local model is closed. -/
theorem isClosed_localModelForm : (localModelForm 𝔪 ωV).IsClosed :=
  ωV.isClosed_constSmooth.mpullback Prod.snd
    (contDiff_snd (𝕜 := ℝ) (E := StrongDual ℝ 𝔪) (F := V)).contMDiff

variable [DistribMulAction K (StrongDual ℝ 𝔪)]
  [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, StrongDual ℝ 𝔪 × V) ∞ K (StrongDual ℝ 𝔪 × V)]

/-- **The fibre form of the local model is `K`-invariant** when `K` acts on `V` by linear
symplectomorphisms. -/
theorem mpullback_smul_localModelForm (hω : ∀ (k : K) (u w : V), ωV (k • u) (k • w) = ωV u w)
    (k : K) :
    SmoothForm.mpullback (fun p : StrongDual ℝ 𝔪 × V ↦ k • p)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) (localModelForm 𝔪 ωV) =
      localModelForm 𝔪 ωV := by
  rw [localModelForm, SmoothForm.mpullback_mpullback_of_comp_eq _ _ contDiff_snd.contMDiff
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, V)) k)
    (funext fun p ↦ Prod.smul_snd k p), ωV.mpullback_smul_constSmooth 𝓘(ℝ, F) (hω k)]

variable [FiniteDimensional ℝ F] [LieGroup 𝓘(ℝ, F) ∞ K]

/-- **The fibre moment map of the local model restricts to a moment map of `K`.** The restriction
`p ↦ f p ∘ ι` of `f` to the Lie algebra `𝔨` of `K` is the moment map `ν ∘ ι + μ_V ∘ pr_V` of the
action of `K` on `(𝔪* × V, pr_V^* ω)`, when `P` vanishes on `𝔨` and `R` restricts to the identity
of `𝔨`. -/
theorem isMomentMap_localModelForm (hω : ∀ (k : K) (u w : V), ωV (k • u) (k • w) = ωV u w)
    (hPι : ∀ κ : GroupLieAlgebra 𝓘(ℝ, F) K, P (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ) = 0)
    (hRι : ∀ κ : GroupLieAlgebra 𝓘(ℝ, F) K, R (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ) = κ) :
    (localModelForm 𝔪 ωV).IsMomentMap
      (InfinitesimalAction.fundamental 𝓘(ℝ, F) K 𝓘(ℝ, StrongDual ℝ 𝔪 × V) (StrongDual ℝ 𝔪 × V))
      fun p ↦ (localModelMap ωV ν P R p : E →ₗ[ℝ] ℝ) ∘ₗ
        (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap := by
  -- The projection `pr_V` is equivariant, so it relates the fundamental vector fields.
  have hrel (κ : GroupLieAlgebra 𝓘(ℝ, F) K) (p : StrongDual ℝ 𝔪 × V) :
      mfderiv 𝓘(ℝ, StrongDual ℝ 𝔪 × V) 𝓘(ℝ, V) Prod.snd p
        (InfinitesimalAction.fundamental 𝓘(ℝ, F) K 𝓘(ℝ, StrongDual ℝ 𝔪 × V)
          (StrongDual ℝ 𝔪 × V) κ p) =
        InfinitesimalAction.fundamental 𝓘(ℝ, F) K 𝓘(ℝ, V) V κ p.2 := by
    rw [InfinitesimalAction.fundamental_apply, InfinitesimalAction.fundamental_apply]
    exact mfderiv_fundamentalVectorField_of_map_smul
      ((contDiff_snd (n := 1)).contMDiff.mdifferentiableAt one_ne_zero)
      ((ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, F)) (n := ∞) p).mdifferentiableAt
        (by simp)) (fun k ↦ Prod.smul_snd k p) κ
  have h := ((ωV.isMomentMap_linearActionMomentMap (I := 𝓘(ℝ, F)) hω).mpullback
    contDiff_snd.contMDiff hrel).add_const
    ((ν : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap)
  rw [localModelForm]
  convert h using 1
  funext p
  ext κ
  -- `(f p ∘ ι) κ` is `f p (ι κ)` by definition of the composition.
  have hκ := localModelMap_apply ωV ν P R p (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ)
  rw [hPι, hRι, map_zero, add_zero, add_comm] at hκ
  exact hκ

variable [LieGroup I ∞ G]

omit [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, StrongDual ℝ 𝔪 × V) ∞ K (StrongDual ℝ 𝔪 × V)] in
/-- **The fibre moment map of the local model is equivariant**, `f (k • p) = Ad*_k (f p)`, when
`ν` is fixed by the coadjoint action of `K`, `a ↦ a ∘ P` intertwines the action of `K` on `𝔪*` with
its coadjoint action, `R` intertwines the adjoint actions, and `K` acts on `V` by linear
symplectomorphisms. -/
theorem localModelMap_smul
    (hν : ∀ k : K, ν.comp (Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹) = ν)
    (hPK : ∀ (k : K) (a : StrongDual ℝ 𝔪),
      (k • a).comp P = (a.comp P).comp (Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹))
    (hR : ∀ (k : K) (ξ : E), R (Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹ ξ) =
      Lie.adjointContinuousLinearMap (I := 𝓘(ℝ, F)) k⁻¹ (R ξ))
    (hω : ∀ (k : K) (u w : V), ωV (k • u) (k • w) = ωV u w) (k : K) (p : StrongDual ℝ 𝔪 × V) :
    localModelMap ωV ν P R (k • p) =
      (localModelMap ωV ν P R p).comp (Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹) := by
  ext ξ
  set Ad := Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹
  have hμ := (ωV.isEquivariantMomentMap_linearActionMomentMap (I := 𝓘(ℝ, F)) hω).apply_smul k p.2
  -- A composite `φ ∘ Ad_{k⁻¹}` evaluates at `ξ` to `φ (Ad_{k⁻¹} ξ)` by definition.
  have h₁ : ν (Ad ξ) = ν ξ := DFunLike.congr_fun (hν k) ξ
  have h₂ : (k • p.1) (P ξ) = p.1 (P (Ad ξ)) := DFunLike.congr_fun (hPK k p.1) ξ
  trans ν (Ad ξ) + p.1 (P (Ad ξ)) +
    SymplecticForm.linearActionMomentMap 𝓘(ℝ, F) K ωV p.2 (R (Ad ξ))
  · rw [localModelMap_apply, Prod.smul_fst, Prod.smul_snd, hμ, Lie.coadjointRepresentation_apply,
      ← hR, h₁, h₂]
  · exact (localModelMap_apply ωV ν P R p _).symm

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] [LieGroup 𝓘(ℝ, F) ∞ K]
  [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, StrongDual ℝ 𝔪 × V) ∞ K (StrongDual ℝ 𝔪 × V)] in
/-- **The moment map of the local model on its zero orbit**: at `[g, 0, 0]` the moment map
`[g, a, v] ↦ Ad*_g (ν + a ∘ P + μ_V(v) ∘ R)` of the local model is `Ad*_g ν`; in particular it
takes the value `ν` at the base point `[1, 0, 0]`. -/
theorem balancedProductInducedMomentMap_localModelMap_mk_zero
    (hfK : ∀ (k : K) (p : StrongDual ℝ 𝔪 × V), localModelMap ωV ν P R (k • p) =
      localModelMap ωV ν P R p ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹) (g : G) :
    balancedProductInducedMomentMap G hfK
        (BalancedProduct.mk K (K.toRightTranslation g) (0 : StrongDual ℝ 𝔪 × V)) =
      Lie.coadjointRepresentation ℝ I G g (ν : E →ₗ[ℝ] ℝ) := by
  rw [balancedProductInducedMomentMap_mk, localModelMap_zero]

/-! ### The local model `G ×_K (𝔪* × V)` -/

section BalancedProduct

variable [FiniteDimensional ℝ 𝔪] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G] [I.Boundaryless]
  [IsClosed (K : Set G)]
  {hf : ContMDiff 𝓘(ℝ, StrongDual ℝ 𝔪 × V) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ (localModelMap ωV ν P R)}
  {hfK : ∀ (k : K) (p : StrongDual ℝ 𝔪 × V), localModelMap ωV ν P R (k • p) =
    localModelMap ωV ν P R p ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹}
  {hσK : ∀ k : K, SmoothForm.mpullback (fun p : StrongDual ℝ 𝔪 × V ↦ k • p)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) (localModelForm 𝔪 ωV) =
      localModelForm 𝔪 ωV}
  {hμ : (localModelForm 𝔪 ωV).IsMomentMap
    (InfinitesimalAction.fundamental 𝓘(ℝ, F) K 𝓘(ℝ, StrongDual ℝ 𝔪 × V) (StrongDual ℝ 𝔪 × V))
    fun p ↦ (localModelMap ωV ν P R p : E →ₗ[ℝ] ℝ) ∘ₗ
      (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap}

/-- **The form of the local model at its base point.** On images of tangent vectors
`(ξ, a, u)` and `(ζ, b, w)` at `(1, 0, 0)`, the induced form of `G ×_K (𝔪* × V)` is

`b(P ξ) - a(P ζ) + ν ⁅ξ, ζ⁆ + ω(u, w)`:

the pairing of `𝔪` with `𝔪*`, the Kirillov–Kostant–Souriau tensor of `ν` and the symplectic form
of the slice. -/
theorem eval₂_balancedProductInducedForm_localModelForm_mfderiv_one_zero
    (v w : TangentSpace (I.prod 𝓘(ℝ, StrongDual ℝ 𝔪 × V))
      (K.toRightTranslation 1, (0 : StrongDual ℝ 𝔪 × V))) :
    letI := BalancedProduct.rightTranslationChartedSpace K (StrongDual ℝ 𝔪 × V) I
      𝓘(ℝ, StrongDual ℝ 𝔪 × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := StrongDual ℝ 𝔪 × V)
      (I := I) (IZ := 𝓘(ℝ, StrongDual ℝ 𝔪 × V)) (F := F)
    (balancedProductInducedForm I G (localModelForm 𝔪 ωV) hf hfK hσK hμ).eval₂
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × (StrongDual ℝ 𝔪 × V)))
          (K.toRightTranslation 1, 0))
        (mfderiv (I.prod 𝓘(ℝ, StrongDual ℝ 𝔪 × V))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (StrongDual ℝ 𝔪 × V)))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × (StrongDual ℝ 𝔪 × V)))) _ v)
        (mfderiv (I.prod 𝓘(ℝ, StrongDual ℝ 𝔪 × V))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (StrongDual ℝ 𝔪 × V)))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × (StrongDual ℝ 𝔪 × V)))) _ w) =
      w.2.1 (P v.1) - v.2.1 (P w.1) +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (ν : E →ₗ[ℝ] ℝ) v.1 w.1 +
        ωV v.2.2 w.2.2 := by
  rw [eval₂_balancedProductInducedForm_mfderiv_one]
  have hw := mvfderiv_localModelMap_zero ωV ν P R w.2
  have hv := mvfderiv_localModelMap_zero ωV ν P R v.2
  have hσ := eval₂_localModelForm ωV 0 v.2 w.2
  simp only [hw, hv, hσ, localModelMap_zero]
  -- `(b ∘ P) ξ` is `b (P ξ)` and the Kirillov form of `ν` is read through `ν : 𝔤 →ₗ ℝ`, both by
  -- definition.
  rfl

variable (hPν : ∀ m : 𝔪, ∃ κ : GroupLieAlgebra I G,
    (∀ ζ : GroupLieAlgebra I G, ν (⁅κ, ζ⁆ : GroupLieAlgebra I G) = 0) ∧ P κ = m)
  (hKν : ∀ ξ : GroupLieAlgebra I G,
    (∀ ζ : GroupLieAlgebra I G, ν (⁅ξ, ζ⁆ : GroupLieAlgebra I G) = 0) → P ξ = 0 →
      ∃ κ : GroupLieAlgebra 𝓘(ℝ, F) K, K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ = ξ)
include hPν hKν

/-- **The local model is nondegenerate along its zero orbit.** Suppose that `P` maps the coadjoint
stabilizer `𝔤_ν = {ξ | ν ⁅ξ, ·⁆ = 0}` onto `𝔪`, and that every `ξ ∈ 𝔤_ν` with `P ξ = 0` lies in `𝔨`;
for the model, where `P` is the projection onto `𝔪` along `𝔨 ⊕ 𝔮`, this says `𝔤_ν = 𝔨 ⊕ 𝔪`. Then
the induced form of `G ×_K (𝔪* × V)` is nondegenerate at every point `[g, 0, 0]`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm_mk (g : G) :
    letI := BalancedProduct.rightTranslationChartedSpace K (StrongDual ℝ 𝔪 × V) I
      𝓘(ℝ, StrongDual ℝ 𝔪 × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := StrongDual ℝ 𝔪 × V)
      (I := I) (IZ := 𝓘(ℝ, StrongDual ℝ 𝔪 × V)) (F := F)
    ((balancedProductInducedForm I G (localModelForm 𝔪 ωV) hf hfK hσK hμ).bilinFormAt
        (BalancedProduct.mk K (K.toRightTranslation g)
          (0 : StrongDual ℝ 𝔪 × V))).Nondegenerate := by
  -- Identify `T₀(𝔪* × V)` with `𝔪* × V`, read with the algebraic dual of `𝔪`.
  let e : (StrongDual ℝ 𝔪 × V) ≃ₗ[ℝ] Module.Dual ℝ 𝔪 × V :=
    LinearMap.toContinuousLinearMap.symm.prodCongr (LinearEquiv.refl ℝ V)
  have h1 := nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one (hf := hf) (hfK := hfK)
    (hσK := hσK) (hμ := hμ) (n := (0 : StrongDual ℝ 𝔪 × V)) (fun k ↦ smul_zero k) e
    P.toLinearMap ωV.nondegenerate.1
    -- `(a ∘ P) ξ` is the algebraic dual vector of `a` evaluated at `P ξ`, by definition.
    (fun u ξ ↦ by rw [mvfderiv_localModelMap_zero]; rfl)
    (fun u w ↦ eval₂_localModelForm ωV 0 u w) (by rw [localModelMap_zero]; exact hPν)
    (by rw [localModelMap_zero]; exact hKν)
  exact (nondegenerate_bilinFormAt_balancedProductInducedForm_mk_iff g 0).2 h1

/-- **The local model is symplectic near its zero orbit.** Under the hypotheses of
`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm_mk`,
the induced form of `G ×_K (𝔪* × V)` is nondegenerate on an open `G`-invariant set containing the
zero orbit `{[g, 0, 0]}`. -/
theorem exists_isOpen_nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm :
    letI := BalancedProduct.rightTranslationChartedSpace K (StrongDual ℝ 𝔪 × V) I
      𝓘(ℝ, StrongDual ℝ 𝔪 × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := StrongDual ℝ 𝔪 × V)
      (I := I) (IZ := 𝓘(ℝ, StrongDual ℝ 𝔪 × V)) (F := F)
    ∃ U : Set (BalancedProduct K K.RightTranslation (StrongDual ℝ 𝔪 × V)), IsOpen U ∧
      (∀ (g : G) (y : BalancedProduct K K.RightTranslation (StrongDual ℝ 𝔪 × V)),
        y ∈ U → g • y ∈ U) ∧
      (∀ g : G, BalancedProduct.mk K (K.toRightTranslation g) (0 : StrongDual ℝ 𝔪 × V) ∈ U) ∧
      ∀ y ∈ U, ((balancedProductInducedForm I G (localModelForm 𝔪 ωV) hf hfK hσK hμ).bilinFormAt
        y).Nondegenerate :=
  exists_isOpen_nondegenerate_bilinFormAt_balancedProductInducedForm
    (nondegenerate_bilinFormAt_balancedProductInducedForm_localModelForm_mk ωV ν P R hPν hKν 1)

end BalancedProduct

end TauCeti.CotangentBundle
