/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
import TauCeti.Geometry.Contact.Levi
import TauCeti.Geometry.Contact.Pullback

/-!
# The normal bundle of a Legendrian embedding

Let `α` be a contact form on a manifold `N` of dimension `2 k + 1`, and let `f : M → N` be a
smooth embedding which is a Legendrian immersion for the contact structure `ker α`, so that `M`
has dimension `k`. At each point `x` of `M`, an ambient tangent vector `v` at `f x` gives the pair

`(dα_(f x)(df_x ·, v), α_(f x)(v)) ∈ T_x^* M × ℝ`

(`TauCeti.SmoothEmbedding.contactPairing`). It vanishes exactly when `v` is tangent to the
embedded Legendrian submanifold
(`TauCeti.SmoothEmbedding.contactPairing_eq_zero_iff_mem_tangentRange`): if `α(v) = 0` then `v`
lies in the contact hyperplane, and if moreover `dα(df ·, v) = 0` then `v` is Levi-orthogonal to
the tangent image, which is maximal isotropic for the Levi form. So the pair descends to an
injective map on the normal space `T_(f x) N ⧸ df_x(T_x M)`, which is bijective because both sides
have dimension `k + 1`. This gives the fibrewise isomorphism
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`)

`T_(f x) N ⧸ df_x(T_x M) ≃ T_x^* M × ℝ`, `[v] ↦ (dα(df ·, v), α(v))`.

The second factor is spanned by the class of the Reeb vector field, which corresponds to `(0, 1)`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion_normalClass_reebVectorField`),
and the classes of vectors in the contact hyperplane are those with second component zero.

These isomorphisms depend smoothly on `x`, so the normal bundle of the embedding is
`C^m`-diffeomorphic to `T^* M × ℝ` over the identity of `M`
(`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLegendrianImmersion`). The target is the
carrier `J¹M = T^* M × ℝ` of the one-jet contact form `dz - λ_M`. Combined with a tubular
neighbourhood, this identifies a neighbourhood of a Legendrian submanifold with a neighbourhood of
the zero section of `J¹M` to first order, the linear input of the Legendrian neighbourhood theorem.
It is the contact counterpart of the identification of the normal bundle of a Lagrangian embedding
with its cotangent bundle (`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`),
whose pairing covector `σ(df ·, v)` is reused here for `σ = dα`. Both are instances of the
identification of a normal bundle by a smooth family of maps with kernels the tangent ranges
(`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (neighbourhoods of Legendrian submanifolds).
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

open SmoothForm

variable {E F P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n m : ℕ∞ω} {α : SmoothForm J N ℝ 1}
  (f : SmoothEmbedding I J n M N)

/-- The pair `(dα_(f x)(df_x ·, v), α_(f x)(v))` attached to an ambient tangent vector `v` at
`f x`, as a continuous linear function of `v` with values in `T_x^* M × ℝ`. Its first component is
the pairing covector of the two-form `dα`. -/
def contactPairing (α : SmoothForm J N ℝ 1) (x : M) :
    TangentSpace J (f x) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) × ℝ :=
  (f.pairingCovector (mextDerivₗ J 1 α) x).prod (degreeOneEquiv α (f x))

/-- The first component of the contact pairing of `v` is the covector `dα(df ·, v)`. -/
@[simp]
theorem contactPairing_apply_fst (α : SmoothForm J N ℝ 1) (x : M) (v : TangentSpace J (f x)) :
    (f.contactPairing α x v).1 = f.pairingCovector (mextDerivₗ J 1 α) x v :=
  (rfl)

/-- The second component of the contact pairing of `v` is `α(v)`. -/
@[simp]
theorem contactPairing_apply_snd (α : SmoothForm J N ℝ 1) (x : M) (v : TangentSpace J (f x)) :
    (f.contactPairing α x v).2 = α.val (f x) ![v] := by
  simp [contactPairing]

/-- The first component of the contact pairing of `v` evaluates on `u` as `dα(df u, v)`. -/
theorem contactPairing_apply_fst_apply (α : SmoothForm J N ℝ 1) (x : M)
    (v : TangentSpace J (f x)) (u : TangentSpace I x) :
    (f.contactPairing α x v).1 u = mextDeriv α.val (f x) ![mfderiv I J f x u, v] := by
  rw [contactPairing_apply_fst, pairingCovector_apply_apply, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply]

/-- **The contact pairings depend smoothly on the ambient tangent vector.** For a `C^n` embedding
with `m + 1 ≤ n` and `m + 1 ≤ ∞`, the map `⟨x, v⟩ ↦ ⟨x, (dα_(f x)(df_x ·, v), α_(f x)(v))⟩` from
the pullback of the ambient tangent bundle to the direct sum of the cotangent bundle `T^* M` and
the trivial line bundle is `C^m`. -/
theorem contMDiff_contactPairing [IsManifold I 1 M] (α : SmoothForm J N ℝ 1) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) :
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) × ℝ)) m
      (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' ((E →L[ℝ] ℝ) × ℝ)
          (E := (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ×ᵇ Trivial M ℝ) p.proj
          (f.contactPairing α p.proj p.snd)) := by
  have : IsManifold J (m + 1) N := .of_le hm'
  have hfm : ContMDiff I J (m + 1) f := f.contMDiff.of_le hm
  -- The covector `α_(f x)` at `f x`, as a function of `⟨x, v⟩`.
  have hα : ContMDiff (I.prod 𝓘(ℝ, F)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) m
      (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : N ↦ TangentSpace J y →L[ℝ] ℝ)
          (f p.proj) (degreeOneEquiv α (f p.proj))) :=
    ((degreeOneEquiv α).contMDiff.of_le (le_self_add.trans hm')).comp
      ((hfm.of_le le_self_add).comp
        (Bundle.contMDiff_proj (F := F) ((f : M → N) *ᵖ (TangentSpace J))))
  have hev := ContMDiff.clm_bundle_apply (F₁ := F) (F₂ := ℝ) (E₁ := TangentSpace J)
    (E₂ := Trivial N ℝ) hα
    (Bundle.Pullback.contMDiff_lift (E := TangentSpace J) f (hfm.of_le le_self_add))
  have hsnd : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, ℝ)) m
      (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' ℝ (E := Trivial M ℝ) p.proj (degreeOneEquiv α (f p.proj) p.snd)) :=
    Trivial.contMDiff_mk_iff.2
      ⟨Bundle.contMDiff_proj (F := F) ((f : M → N) *ᵖ (TangentSpace J)),
        (Trivial.contMDiff_mk_iff.1 hev).2⟩
  exact fun p ↦ Bundle.contMDiffAt_totalSpace_prod_iff.2
    ⟨f.contMDiff_pairingCovector (mextDerivₗ J 1 α) hm hm' p, hsnd p⟩

variable [CompleteSpace F] [FiniteDimensional ℝ F] [IsManifold I 2 M]

/-- **The contact pairing detects tangency to a Legendrian submanifold.** For an embedding which
is a Legendrian immersion for `ker α`, the pair `(dα(df ·, v), α(v))` vanishes exactly when `v` is
tangent to the image. -/
theorem contactPairing_eq_zero_iff_mem_tangentRange
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (x : M)
    (v : TangentSpace J (f x)) :
    f.contactPairing α x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn := by
  rw [Prod.ext_iff, contactPairing_apply_snd, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨hdα, hv⟩
    -- `v` lies in the contact hyperplane and is Levi-orthogonal to the tangent image, since the
    -- linear map `T N ⧸ ker α → ℝ` induced by `α` is injective and carries the Levi form to `dα`.
    refine hf.mem_range_mfderiv_of_distributionLeviForm_eq_zero
      (a := ⟨v, mem_kerDistribution.2 hv⟩) fun u ↦ ?_
    have hinj : Function.Injective ((α.kerDistribution (f x)).liftQ
        (degreeOneEquiv α (f x) : TangentSpace J (f x) →ₗ[ℝ] ℝ) (kerDistribution_def α (f x)).le) :=
      LinearMap.ker_eq_bot.1 <| Submodule.ker_liftQ_eq_bot _ _ _ (kerDistribution_def α (f x)).ge
    refine hinj ?_
    rw [map_zero, liftQ_distributionLeviForm_kerDistribution (hf.isContactForm.apply_ne_zero _),
      mextDeriv_apply_swap, ← contactPairing_apply_fst_apply, hdα, zero_apply, neg_zero]
  · rintro ⟨u', rfl⟩
    refine ⟨ContinuousLinearMap.ext fun u ↦ ?_, mem_kerDistribution.1
      (hf.isHorizontalMap.mfderiv_mem x u')⟩
    have hc : ContMDiff I J ∞ f := hf.isImmersion.contMDiff
    rw [ContinuousLinearMap.coe_coe, contactPairing_apply_fst, pairingCovector_apply_apply,
      ← eval₂_mpullback f hc,
      mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap hc hf.isHorizontalMap]
    simp [SmoothBundleForm.eval₂_apply]

omit [IsManifold I 2 M] in
/-- The codimension of a Legendrian immersion is the dimension of `(E →L[ℝ] ℝ) × ℝ`, so this is a
model fibre for the normal bundle of a Legendrian embedding. -/
theorem finrank_prod_eq_sub_of_isLegendrianImmersion [FiniteDimensional ℝ E] {g : M → N}
    (hg : IsLegendrianImmersion I α.kerDistribution g) :
    finrank ℝ ((E →L[ℝ] ℝ) × ℝ) = finrank ℝ F - finrank ℝ E := by
  have h2 := hg.two_mul_finrank_add_one
  rw [finrank_prod, ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq,
    finrank_self]
  omega

/-- **The normal space of a Legendrian embedding is `T_x^* M × ℝ`.** For an embedding which is a
Legendrian immersion for the kernel of a contact form `α`, the normal class `[v]` of an ambient
tangent vector `v` at `f x` corresponds to the pair `(dα_(f x)(df_x ·, v), α_(f x)(v))`. -/
def normalSpaceEquivOfIsLegendrianImmersion (hf : IsLegendrianImmersion I α.kerDistribution f)
    (hn : n ≠ 0) (x : M) :
    f.isImmersion.NormalSpace x hn ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) × ℝ :=
  haveI : FiniteDimensional ℝ E := f.finiteDimensional_tangentSpace x hn
  f.normalSpaceEquivOfKer x hn (f.contactPairing α x)
    (f.contactPairing_eq_zero_iff_mem_tangentRange hf hn x) <| by
    rw [f.isImmersion.finrank_normalSpace x hn, finrank_tangentSpace, finrank_tangentSpace]
    exact (finrank_prod_eq_sub_of_isLegendrianImmersion hf).symm

/-- The normal class `[v]` of an ambient tangent vector at `f x` corresponds to the pair
`(dα(df ·, v), α(v))`. -/
@[simp]
theorem normalSpaceEquivOfIsLegendrianImmersion_normalClass
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (x : M)
    (v : TangentSpace J (f x)) :
    f.normalSpaceEquivOfIsLegendrianImmersion hf hn x (f.isImmersion.normalClass x hn v) =
      f.contactPairing α x v :=
  haveI : FiniteDimensional ℝ E := f.finiteDimensional_tangentSpace x hn
  f.normalSpaceEquivOfKer_normalClass x hn _ _ _ v

/-- The pair `(dα(df ·, v), α(v))` corresponds to the normal class `[v]`. -/
@[simp]
theorem normalSpaceEquivOfIsLegendrianImmersion_symm_contactPairing
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (x : M)
    (v : TangentSpace J (f x)) :
    (f.normalSpaceEquivOfIsLegendrianImmersion hf hn x).symm (f.contactPairing α x v) =
      f.isImmersion.normalClass x hn v :=
  haveI : FiniteDimensional ℝ E := f.finiteDimensional_tangentSpace x hn
  f.normalSpaceEquivOfKer_symm_apply x hn _ _ _ v

/-- **The Reeb direction spans the trivial factor.** The normal class of the Reeb vector field of
`α` at `f x` corresponds to `(0, 1)`. -/
theorem normalSpaceEquivOfIsLegendrianImmersion_normalClass_reebVectorField
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (x : M) :
    f.normalSpaceEquivOfIsLegendrianImmersion hf hn x
        (f.isImmersion.normalClass x hn (α.reebVectorField (f x))) = (0, 1) := by
  have hα := hf.isContactForm
  rw [normalSpaceEquivOfIsLegendrianImmersion_normalClass, Prod.ext_iff, contactPairing_apply_snd,
    hα.apply_reebVectorField]
  refine ⟨ContinuousLinearMap.ext fun u ↦ ?_, rfl⟩
  rw [contactPairing_apply_fst_apply, hα.mextDeriv_reebVectorField_right, zero_apply]

/-- The pair `(0, 1)` corresponds to the normal class of the Reeb vector field of `α` at `f x`. -/
theorem normalSpaceEquivOfIsLegendrianImmersion_symm_zero_one
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (x : M) :
    (f.normalSpaceEquivOfIsLegendrianImmersion hf hn x).symm (0, 1) =
      f.isImmersion.normalClass x hn (α.reebVectorField (f x)) :=
  (ContinuousLinearEquiv.symm_apply_eq _).2
    (f.normalSpaceEquivOfIsLegendrianImmersion_normalClass_reebVectorField hf hn x).symm

variable [FiniteDimensional ℝ E] [IsManifold I (m + 1) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The identification of the normal bundle of a Legendrian embedding with `T^* M × ℝ` is
smooth.** For a `C^n` embedding which is a Legendrian immersion for the kernel of `α`, with
`m + 1 ≤ n`, the map of total spaces from the intrinsic normal bundle, with model fibre `P` of the
codimension, to the direct sum of the cotangent bundle and the trivial line bundle induced by
`normalSpaceEquivOfIsLegendrianImmersion` is `C^m`. The bound `m + 1 ≤ ∞` reflects that the form
`α` is smooth. -/
theorem contMDiff_normalSpaceEquivOfIsLegendrianImmersion
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) × ℝ)) m
      (fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' ((E →L[ℝ] ℝ) × ℝ)
          (E := (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ×ᵇ Trivial M ℝ) p.proj
          (f.normalSpaceEquivOfIsLegendrianImmersion hf hn p.proj p.snd)) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J (m + 1) N := .of_le hm'
  exact f.contMDiff_normalSpaceEquivOfKer hn hm hdim (f.contactPairing α)
    (f.contactPairing_eq_zero_iff_mem_tangentRange hf hn)
    (fun x ↦ (f.normalSpaceEquivOfIsLegendrianImmersion hf hn x).toLinearEquiv.finrank_eq)
    (f.contMDiff_contactPairing α hm hm')

/-- **The normal bundle of a Legendrian embedding is diffeomorphic to `T^* M × ℝ`.** For a `C^n`
embedding which is a Legendrian immersion for the kernel of a contact form `α`, with `m + 1 ≤ n`
and `m + 1 ≤ ∞`, the intrinsic normal bundle, with model fibre `P` of the codimension, is
`C^m`-diffeomorphic to `T^* M × ℝ` over the identity of `M`, by
`[v] ↦ (dα(df ·, v), α(v))` on each fibre. -/
def normalBundleDiffeomorphOfIsLegendrianImmersion
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)
      ≃ₘ^m⟮I.prod 𝓘(ℝ, P), (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ)⟯ CotangentBundle I M × ℝ :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J (m + 1) N := .of_le hm'
  letI := f.normalSpaceFiberBundle hn hdim
  (f.normalBundleDiffeomorphOfKer hn hm hdim
    (E₂ := (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ×ᵇ Trivial M ℝ) (f.contactPairing α)
    (f.contactPairing_eq_zero_iff_mem_tangentRange hf hn)
    (fun x ↦ (f.normalSpaceEquivOfIsLegendrianImmersion hf hn x).toLinearEquiv.finrank_eq)
    (f.contMDiff_contactPairing α hm hm')).trans
    (Bundle.Prod.diffeomorphProdTrivial I ℝ (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) m)

/-- The diffeomorphism sends a normal vector at `x` to the corresponding pair of a covector at `x`
and a real number. -/
@[simp]
theorem normalBundleDiffeomorphOfIsLegendrianImmersion_apply
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E)
    (p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalBundleDiffeomorphOfIsLegendrianImmersion hf hn hm hm' hdim p =
      (⟨p.proj, (f.normalSpaceEquivOfIsLegendrianImmersion hf hn p.proj p.snd).1⟩,
        (f.normalSpaceEquivOfIsLegendrianImmersion hf hn p.proj p.snd).2) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J (m + 1) N := .of_le hm'
  let := f.normalSpaceFiberBundle hn hdim
  rw [normalBundleDiffeomorphOfIsLegendrianImmersion, Diffeomorph.coe_trans, Function.comp_apply,
    normalBundleDiffeomorphOfKer_apply, Bundle.Prod.diffeomorphProdTrivial_apply]
  rfl

/-- The inverse diffeomorphism sends a covector at `x` and a real number to the corresponding
normal vector at `x`. -/
@[simp]
theorem normalBundleDiffeomorphOfIsLegendrianImmersion_symm_apply
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E)
    (q : CotangentBundle I M × ℝ) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalBundleDiffeomorphOfIsLegendrianImmersion hf hn hm hm' hdim).symm q =
      ⟨q.1.proj,
        (f.normalSpaceEquivOfIsLegendrianImmersion hf hn q.1.proj).symm (q.1.snd, q.2)⟩ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J (m + 1) N := .of_le hm'
  let := f.normalSpaceFiberBundle hn hdim
  rw [normalBundleDiffeomorphOfIsLegendrianImmersion, Diffeomorph.symm_trans',
    Diffeomorph.coe_trans, Function.comp_apply, Bundle.Prod.diffeomorphProdTrivial_symm_apply,
    normalBundleDiffeomorphOfKer_symm_apply]
  rfl

/-- The diffeomorphism sends the normal class `[v]` at `x` to the covector `dα(df ·, v)` at `x`
together with `α(v)`. -/
theorem normalBundleDiffeomorphOfIsLegendrianImmersion_normalClass
    (hf : IsLegendrianImmersion I α.kerDistribution f) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E) (x : M)
    (v : TangentSpace J (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalBundleDiffeomorphOfIsLegendrianImmersion hf hn hm hm' hdim
        ⟨x, f.isImmersion.normalClass x hn v⟩ =
      (⟨x, f.pairingCovector (mextDerivₗ J 1 α) x v⟩, α.val (f x) ![v]) := by
  rw [normalBundleDiffeomorphOfIsLegendrianImmersion_apply,
    normalSpaceEquivOfIsLegendrianImmersion_normalClass, contactPairing_apply_fst,
    contactPairing_apply_snd]

end TauCeti.SmoothEmbedding
