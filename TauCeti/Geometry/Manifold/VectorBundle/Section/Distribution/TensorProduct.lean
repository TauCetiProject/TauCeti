/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SchwartzKernel

/-!
# External tensor products of distribution densities on manifolds

Let `M` and `N` be boundaryless Hausdorff `σ`-compact smooth manifolds with finite-dimensional
models. The continuous linear functionals on the scalar tests on `M`, the compactly supported
smooth real functions, are the distribution densities on `M`; we take their values in a complete
normed `ℝ`-algebra `A`, for instance `ℝ` or `ℂ`. The **external tensor product** of a functional
`S` on `M` and a functional `T` on `N` is the functional `S ⊠ T` on the scalar tests on `M × N`
determined by its values on tensor products of tests,

`(S ⊠ T) (φ ⊗ ψ) = S φ * T ψ`

(`TauCeti.BundleTest.tensorProduct`, `TauCeti.BundleTest.tensorProduct_tensor`). It exists and is
unique by the Schwartz kernel theorem on manifolds
(`LinearMap.existsUnique_schwartzKernel_tensor_of_continuous`), applied to the separately
continuous bilinear map `(φ, ψ) ↦ S φ * T ψ`, and uniqueness gives the characterization
`TauCeti.BundleTest.eq_tensorProduct_iff`. This is the manifold form of the Euclidean tensor
product of distributions (`Distribution.tensorProduct`).

From the characterization:

* the tensor product is bilinear (`TauCeti.BundleTest.add_tensorProduct`,
  `TauCeti.BundleTest.smul_tensorProduct`, …);
* multiplying `S ⊠ T` by `(x, y) ↦ f x * g y` multiplies `S` by `f` and `T` by `g`
  (`TauCeti.BundleTest.smulLeftDualCLM_mulProd_tensorProduct`);
* the tensor product of point masses is the point mass at the pair of points,
  `δ_x a ⊠ δ_y b = δ_(x, y) (a * b)` (`TauCeti.BundleTest.tensorProduct_delta`);
* the support of `S ⊠ T` lies in `supp S × supp T`
  (`TauCeti.BundleTest.dsupport_tensorProduct_subset`), with equality when `A` has no zero
  divisors (`TauCeti.BundleTest.dsupport_tensorProduct`);
* pushforward commutes with the tensor product: if `f` is proper on the support of `S` and `g` on
  that of `T`, then `f × g` is proper on the support of `S ⊠ T`
  (`TauCeti.BundleTest.IsProperOnSupport.tensorProduct`) and
  `(f × g)_* (S ⊠ T) = f_* S ⊠ g_* T` (`TauCeti.BundleTest.pushforward_tensorProduct`), and
  likewise for pushforward along proper maps (`TauCeti.BundleTest.pushforwardCLM_tensorProduct`).

The support bound is the localization step behind the wave front set bound for tensor products,
and the product of two distributions on a manifold is the pullback of their external tensor
product along the diagonal.

## Main declarations

* `TauCeti.BundleTest.tensorProduct`: the external tensor product `S ⊠ T`.
* `TauCeti.BundleTest.tensorProduct_tensor`: `(S ⊠ T) (φ ⊗ ψ) = S φ * T ψ`.
* `TauCeti.BundleTest.eq_tensorProduct_iff`: the tensor product is the only functional with these
  values.
* `TauCeti.BundleTest.dsupport_tensorProduct_subset`, `TauCeti.BundleTest.dsupport_tensorProduct`:
  its support.
* `TauCeti.BundleTest.pushforward_tensorProduct`: compatibility with pushforward.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.1.1 (the tensor product of distributions) and §6.3 (distributions and
  densities on manifolds).
* C. Brouder, N. V. Dang and F. Hélein, *Continuity of the fundamental operations on
  distributions having a specified wave front set (with a counter example by Semyon Alesker)*,
  Studia Math. 232 (2016), arXiv:1409.7662v2, §§3–4 (pushforward and tensor products of
  distributions).
-/

public noncomputable section

open Bundle Set Filter Function
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-! ### Definition and characterization -/

/-- The bilinear map `(φ, ψ) ↦ S φ * T ψ` on scalar tests. -/
private def mulPairing (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    BundleTest I ℝ (Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Trivial N ℝ) →ₗ[ℝ] A :=
  (LinearMap.mul ℝ A).compl₁₂ (S : BundleTest I ℝ (Trivial M ℝ) →ₗ[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →ₗ[ℝ] A)

private theorem existsUnique_tensorProduct (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    ∃! K : BundleTest (I.prod J) ℝ (Trivial (M × N) ℝ) →L[ℝ] A,
      ∀ φ ψ, K (φ.tensor ψ) = S φ * T ψ :=
  LinearMap.existsUnique_schwartzKernel_tensor_of_continuous (mulPairing S T)
    (fun _ ↦ S.continuous.mul continuous_const) fun _ ↦ continuous_const.mul T.continuous

/-- The **external tensor product** `S ⊠ T` of a distribution density `S` on `M` and a distribution
density `T` on `N`, continuous linear functionals on the scalar tests with values in a complete
normed algebra `A`: the functional on the scalar tests on `M × N` with
`(S ⊠ T) (φ ⊗ ψ) = S φ * T ψ` (`TauCeti.BundleTest.tensorProduct_tensor`), which determines it
(`TauCeti.BundleTest.eq_tensorProduct_iff`). -/
def tensorProduct (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    BundleTest (I.prod J) ℝ (Trivial (M × N) ℝ) →L_c[ℝ] A :=
  (existsUnique_tensorProduct S T).exists.choose

/-- The tensor product `S ⊠ T` pairs with a tensor product of scalar tests as
`(S ⊠ T) (φ ⊗ ψ) = S φ * T ψ`. -/
@[simp]
theorem tensorProduct_tensor (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) (φ : BundleTest I ℝ (Trivial M ℝ))
    (ψ : BundleTest J ℝ (Trivial N ℝ)) :
    tensorProduct S T (φ.tensor ψ) = S φ * T ψ :=
  (existsUnique_tensorProduct S T).exists.choose_spec φ ψ

/-- **Uniqueness of the tensor product.** A functional on the scalar tests on `M × N` is `S ⊠ T`
exactly when it pairs with every tensor product `φ ⊗ ψ` as `S φ * T ψ`. -/
theorem eq_tensorProduct_iff {S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A}
    {T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A}
    {K : BundleTest (I.prod J) ℝ (Trivial (M × N) ℝ) →L_c[ℝ] A} :
    K = tensorProduct S T ↔ ∀ φ ψ, K (φ.tensor ψ) = S φ * T ψ :=
  ⟨fun h ↦ h ▸ tensorProduct_tensor S T, fun h ↦ ext_tensor fun φ ψ ↦
    (h φ ψ).trans (tensorProduct_tensor S T φ ψ).symm⟩

/-! ### Bilinearity -/

section Bilinear

variable (S S' : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
  (T T' : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A)

/-- The tensor product with the zero functional on the left vanishes. -/
@[simp]
theorem zero_tensorProduct : tensorProduct (0 : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A) T = 0 :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp).symm

/-- The tensor product with the zero functional on the right vanishes. -/
@[simp]
theorem tensorProduct_zero : tensorProduct S (0 : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) = 0 :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp).symm

/-- The tensor product is additive in its first factor. -/
theorem add_tensorProduct : tensorProduct (S + S') T = tensorProduct S T + tensorProduct S' T :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp [add_mul]).symm

/-- The tensor product is additive in its second factor. -/
theorem tensorProduct_add : tensorProduct S (T + T') = tensorProduct S T + tensorProduct S T' :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp [mul_add]).symm

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 A] [SMulCommClass ℝ 𝕜 A] (c : 𝕜)

/-- The tensor product is homogeneous in its first factor. -/
theorem smul_tensorProduct : tensorProduct (c • S) T = c • tensorProduct S T :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp).symm

/-- The tensor product is homogeneous in its second factor. -/
theorem tensorProduct_smul : tensorProduct S (c • T) = c • tensorProduct S T :=
  (eq_tensorProduct_iff.2 fun φ ψ ↦ by simp).symm

end Bilinear

/-! ### Products with smooth functions and point masses -/

/-- Multiplying `S ⊠ T` by the smooth function `(x, y) ↦ f x * g y` multiplies `S` by `f` and `T`
by `g`. -/
theorem smulLeftDualCLM_mulProd_tensorProduct (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯)
    (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A) (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    smulLeftDualCLM (f.mulProd g) (tensorProduct S T) =
      tensorProduct (smulLeftDualCLM f S) (smulLeftDualCLM g T) :=
  eq_tensorProduct_iff.2 fun φ ψ ↦ by
    rw [smulLeftDualCLM_apply, smulLeftCLM_mulProd_tensor, tensorProduct_tensor,
      smulLeftDualCLM_apply, smulLeftDualCLM_apply]

/-- **The tensor product of point masses** is the point mass at the pair of points:
`δ_x ℓ ⊠ δ_y ℓ' = δ_(x, y) (ℓ 1 * ℓ' 1)`. -/
@[simp]
theorem tensorProduct_delta (x : M) (y : N) (ℓ ℓ' : ℝ →L[ℝ] A) :
    tensorProduct (delta (I := I) (F := ℝ) (V := Trivial M ℝ) x ℓ)
        (delta (I := J) (F := ℝ) (V := Trivial N ℝ) y ℓ') =
      delta (I := I.prod J) (F := ℝ) (V := Trivial (M × N) ℝ) (x, y)
        (ContinuousLinearMap.toSpanSingleton ℝ (ℓ 1 * ℓ' 1)) := by
  refine (eq_tensorProduct_iff.2 fun φ ψ ↦ ?_).symm
  have hℓ (ℓ : ℝ →L[ℝ] A) (t : ℝ) : ℓ t = t • ℓ 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  simp only [delta_apply, tensor_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hℓ ℓ (φ x), hℓ ℓ' (ψ y), smul_mul_smul_comm]

/-! ### Supports -/

omit [I.Boundaryless] [CompleteSpace A] in
/-- A smooth function equal to one near a compact set `L` off the support of `S`, whose product
with `S` vanishes. -/
private theorem exists_eventually_eq_one_smulLeftDualCLM_eq_zero {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P] (S : BundleTest I ℝ (Trivial P ℝ) →L_c[ℝ] A)
    {L : Set P} (hL : IsCompact L) (hLS : L ⊆ (dsupport S)ᶜ) :
    ∃ ρ : C^∞⟮I, P; ℝ⟯, (∀ᶠ x in 𝓝ˢ L, ρ x = 1) ∧ smulLeftDualCLM ρ S = 0 := by
  obtain ⟨ρ, hρ, hρ1, -, hρS, -⟩ :=
    hL.exists_contMDiff_one_nhds_tsupport_subset I (isClosed_dsupport S).isOpen_compl hLS
  refine ⟨⟨ρ, hρ⟩, hρ1, DFunLike.coe_injective <| (dsupport_eq_empty_iff _).1 ?_⟩
  exact subset_empty_iff.1 ((dsupport_smulLeftDualCLM_subset _ S).trans fun x hx ↦ hρS hx.2 hx.1)

/-- `S ⊠ T` agrees with `ρ S ⊠ σ T` on the tests on whose support `ρ x * σ y = 1`. -/
private theorem tensorProduct_apply_eq_of_eqOn (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) {ρ : C^∞⟮I, M; ℝ⟯} {σ : C^∞⟮J, N; ℝ⟯}
    {Φ : BundleTest (I.prod J) ℝ (Trivial (M × N) ℝ)}
    (h : ∀ z ∈ closure {z | Φ z ≠ 0}, ρ z.1 * σ z.2 = 1) :
    tensorProduct S T Φ = tensorProduct (smulLeftDualCLM ρ S) (smulLeftDualCLM σ T) Φ := by
  rw [← smulLeftDualCLM_mulProd_tensorProduct, smulLeftDualCLM_apply]
  congr 1
  refine BundleTest.ext fun z ↦ ?_
  rw [smulLeftCLM_apply, ContMDiffMap.mulProd_apply]
  by_cases hz : z ∈ closure {z | Φ z ≠ 0}
  · rw [h z hz, one_smul]
  · simp [Bundle.apply_eq_zero_of_notMem_closure hz]

/-- `S ⊠ T` vanishes on the tests supported off `supp S × N`. -/
private theorem isVanishingOn_tensorProduct_of_left (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    IsVanishingOn (tensorProduct S T) ((dsupport S)ᶜ ×ˢ univ) := by
  refine isVanishingOn_iff.2 fun Φ hΦ ↦ ?_
  obtain ⟨ρ, hρ1, hρS⟩ := exists_eventually_eq_one_smulLeftDualCLM_eq_zero S
    (Φ.isCompact_tsupport.image continuous_fst) (image_subset_iff.2 fun _ hz ↦ (hΦ hz).1)
  rw [tensorProduct_apply_eq_of_eqOn S T (ρ := ρ) (σ := 1) fun z hz ↦ by
    simp [hρ1.self_of_nhdsSet _ (mem_image_of_mem _ hz)]]
  simp [hρS]

/-- `S ⊠ T` vanishes on the tests supported off `M × supp T`. -/
private theorem isVanishingOn_tensorProduct_of_right (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    IsVanishingOn (tensorProduct S T) (univ ×ˢ (dsupport T)ᶜ) := by
  refine isVanishingOn_iff.2 fun Φ hΦ ↦ ?_
  obtain ⟨σ, hσ1, hσT⟩ := exists_eventually_eq_one_smulLeftDualCLM_eq_zero T
    (Φ.isCompact_tsupport.image continuous_snd) (image_subset_iff.2 fun _ hz ↦ (hΦ hz).2)
  rw [tensorProduct_apply_eq_of_eqOn S T (ρ := 1) (σ := σ) fun z hz ↦ by
    simp [hσ1.self_of_nhdsSet _ (mem_image_of_mem _ hz)]]
  simp [hσT]

/-- **The support of a tensor product** lies in the product of the supports:
`supp (S ⊠ T) ⊆ supp S × supp T`. -/
theorem dsupport_tensorProduct_subset (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    dsupport (tensorProduct S T) ⊆ dsupport S ×ˢ dsupport T := by
  intro z hz
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact notMem_dsupport_iff.2 ⟨_, (isClosed_dsupport S).isOpen_compl.prod isOpen_univ,
      ⟨h, mem_univ _⟩, isVanishingOn_tensorProduct_of_left S T⟩ hz
  · exact notMem_dsupport_iff.2 ⟨_, isOpen_univ.prod (isClosed_dsupport T).isOpen_compl,
      ⟨mem_univ _, h⟩, isVanishingOn_tensorProduct_of_right S T⟩ hz

/-- **The support of a tensor product** is the product of the supports,
`supp (S ⊠ T) = supp S × supp T`, when `A` has no zero divisors. -/
theorem dsupport_tensorProduct [NoZeroDivisors A] (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A)
    (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    dsupport (tensorProduct S T) = dsupport S ×ˢ dsupport T := by
  refine (dsupport_tensorProduct_subset S T).antisymm fun z hz ↦ ?_
  by_contra hzST
  obtain ⟨W, hW, hzW, hSTW⟩ := notMem_dsupport_iff.1 hzST
  obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ := isOpen_prod_iff.1 hW z.1 z.2 hzW
  -- Tests supported in `U` and in `V` on which `S` and `T` do not vanish.
  obtain ⟨φ, hφU, hφ⟩ :
      ∃ φ : BundleTest I ℝ (Trivial M ℝ), closure {x | φ x ≠ 0} ⊆ U ∧ S φ ≠ 0 := by
    by_contra! h
    exact notMem_dsupport_iff.2 ⟨U, hU, hzU, isVanishingOn_iff.2 h⟩ hz.1
  obtain ⟨ψ, hψV, hψ⟩ :
      ∃ ψ : BundleTest J ℝ (Trivial N ℝ), closure {y | ψ y ≠ 0} ⊆ V ∧ T ψ ≠ 0 := by
    by_contra! h
    exact notMem_dsupport_iff.2 ⟨V, hV, hzV, isVanishingOn_iff.2 h⟩ hz.2
  have h := isVanishingOn_iff.1 hSTW (φ.tensor ψ) ((tsupport_tensor_subset φ ψ).trans
    ((prod_mono hφU hψV).trans hUV))
  rw [tensorProduct_tensor] at h
  exact mul_ne_zero hφ hψ h

/-! ### Pushforward -/

section Pushforward

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {K : ModelWithCorners ℝ F G} [K.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace G X] [IsManifold K ∞ X] [T2Space X]
  [SigmaCompactSpace X]
  {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [TopologicalSpace G'] {K' : ModelWithCorners ℝ F' G'} [K'.Boundaryless]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace G' Y] [IsManifold K' ∞ Y] [T2Space Y]
  [SigmaCompactSpace Y]
  {S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A} {T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A}
  {f : C^∞⟮I, M; K, X⟯} {g : C^∞⟮J, N; K', Y⟯}

omit [FiniteDimensional ℝ F] [K.Boundaryless] [IsManifold K ∞ X] [SigmaCompactSpace X]
  [FiniteDimensional ℝ F'] [K'.Boundaryless] [IsManifold K' ∞ Y] [SigmaCompactSpace Y] in
/-- If `f` is proper on the support of `S` and `g` on that of `T`, then `f × g` is proper on the
support of `S ⊠ T`. -/
theorem IsProperOnSupport.tensorProduct (hS : IsProperOnSupport ⇑S f)
    (hT : IsProperOnSupport ⇑T g) : IsProperOnSupport ⇑(tensorProduct S T) (f.prodMap g) := by
  rw [isProperOnSupport_iff]
  intro L hL
  refine ((hS.isCompact (hL.image continuous_fst)).prod
    (hT.isCompact (hL.image continuous_snd))).of_isClosed_subset
    ((isClosed_dsupport _).inter (hL.isClosed.preimage (f.prodMap g).contMDiff.continuous))
    fun z hz ↦ ?_
  obtain ⟨hz, hzL⟩ := hz
  obtain ⟨hzS, hzT⟩ := dsupport_tensorProduct_subset S T hz
  exact ⟨⟨hzS, _, hzL, by rw [ContMDiffMap.prodMap_apply]⟩,
    ⟨hzT, _, hzL, by rw [ContMDiffMap.prodMap_apply]⟩⟩

/-- **Pushforward commutes with the tensor product.** If `f` is proper on the support of `S` and
`g` on that of `T`, then `(f × g)_* (S ⊠ T) = f_* S ⊠ g_* T`. -/
theorem pushforward_tensorProduct (hS : IsProperOnSupport ⇑S f) (hT : IsProperOnSupport ⇑T g) :
    pushforward (tensorProduct S T) (f.prodMap g) (hS.tensorProduct hT) =
      tensorProduct (pushforward S f hS) (pushforward T g hT) := by
  refine eq_tensorProduct_iff.2 fun φ ψ ↦ ?_
  -- Tests agreeing with `φ ∘ f` near `supp S` and with `ψ ∘ g` near `supp T`.
  obtain ⟨t, ht⟩ := hS.exists_forall_eventually_eq φ
  obtain ⟨t', ht'⟩ := hT.exists_forall_eventually_eq ψ
  rw [pushforward_apply_of_eventuallyEq hS φ ht, pushforward_apply_of_eventuallyEq hT ψ ht',
    ← tensorProduct_tensor, pushforward_apply_of_eventuallyEq _ _ fun z hz ↦ ?_]
  obtain ⟨hz₁, hz₂⟩ := dsupport_tensorProduct_subset S T hz
  rw [← Prod.mk.eta (p := z), nhds_prod_eq]
  filter_upwards [prod_mem_prod (ht z.1 hz₁) (ht' z.2 hz₂)] with w ⟨hw₁, hw₂⟩
  rw [tensor_apply, tensor_apply, ContMDiffMap.prodMap_apply]
  exact congrArg₂ (· * ·) hw₁ hw₂

/-- Pushforward along proper maps commutes with the tensor product:
`(f × g)_* (S ⊠ T) = f_* S ⊠ g_* T`. -/
theorem pushforwardCLM_tensorProduct (hf : IsProperMap f) (hg : IsProperMap g)
    (S : BundleTest I ℝ (Trivial M ℝ) →L_c[ℝ] A) (T : BundleTest J ℝ (Trivial N ℝ) →L_c[ℝ] A) :
    pushforwardCLM (f.prodMap g) (by simpa using hf.prodMap hg) (tensorProduct S T) =
      tensorProduct (pushforwardCLM f hf S) (pushforwardCLM g hg T) :=
  eq_tensorProduct_iff.2 fun φ ψ ↦ by
    rw [pushforwardCLM_apply, pushforwardCLM_apply, pushforwardCLM_apply, ← tensorProduct_tensor]
    congr 1
    refine BundleTest.ext fun z ↦ ?_
    simp only [compCLM_apply, tensor_apply]
    rw [ContMDiffMap.prodMap_apply]

end Pushforward

end TauCeti.BundleTest
