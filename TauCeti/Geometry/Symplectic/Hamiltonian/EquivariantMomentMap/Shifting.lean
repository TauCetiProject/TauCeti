/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.OrbitLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel

/-!
# The shifting map of a moment map along a coadjoint orbit

Let `μ : M → 𝔤*` be a moment map of an action on `(M, σ)` and let `ι : N → 𝔤*` be a map of a
manifold `N` into a coadjoint orbit `O`, such as the orbit map `G / G_c → 𝔤*`, `[g] ↦ Ad*_g c`.
The **shifting map** is

`Ψ : M × N → 𝔤*`, `Ψ(x, n) = μ(x) - ι(n)`.

Its zero level is the set of pairs `(x, n)` with `μ(x) = ι(n)`, a copy of `μ⁻¹(ι(N))` when
`ι` is injective, and of `μ⁻¹(O)` when `ι` is moreover onto `O`. For an orbit with its
coadjoint-orbit symplectic form reversed, `M × O⁻`, the map `Ψ` is the moment map of the diagonal
action, and the reduced space of `M` at `c` is the reduced space of `M × O⁻` at zero: this is the
shifting trick. As for the level sets of a moment map
(`TauCeti.SmoothTwoForm.IsMomentMap.isRegularPoint_iff_isotropy_eq_bot`), `Ψ` is read in a basis `b`
of `𝔤`, as the map `(x, n) ↦ (μ(x)(b i) - ι(n)(b i))_i` to `ℝ^κ`.

This file proves the following.

* `Ψ` is regular at every point where `μ` is, since `dΨ(v, 0) = dμ(v)`
  (`TauCeti.SmoothTwoForm.IsMomentMap.isRegularPoint_sub_of_surjective`).
* For a coadjoint-equivariant moment map of a Lie group action, if `c` is a regular value of `μ`
  and `ι` takes values in the coadjoint orbit of `c`, then zero is a regular value of `Ψ`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isRegularValue_sub`): by equivariance, `μ` is a
  submersion at every point over the orbit.
* Hence `Ψ⁻¹(0)` is an embedded submanifold of `M × N`. If the tangent images of `ι` are the tangent
  spaces `𝔤 · ι(n)` of the orbit, then the projection `Ψ⁻¹(0) → M`, `(x, n) ↦ x`, has tangent
  image `dμ⁻¹(𝔤 · μ(x)) = ker dμ_x + 𝔤 · x` at `(x, n)`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.range_mfderiv_fst_sub`), and for a nondegenerate
  form it is a coisotropic map
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCoisotropicMap_fst_sub`), whether or not the
  orbit is a point. Its image is `μ⁻¹(ι(N))`; when `ι` is injective, as the orbit map
  `G / G_c → 𝔤*` is, `Ψ⁻¹(0)` is a copy of `μ⁻¹(ι(N))`, and of `μ⁻¹(O)` when `ι` is moreover onto
  `O`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting trick).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

/-! ### Regular points of the shifting map -/

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {κ : Type*} [Fintype κ]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- The shifting map `(x, n) ↦ μ(x) - ι(n)`, read in a basis of `𝔤`, is smooth when the components
of `ι` are. -/
theorem contMDiff_sub (h : σ.IsMomentMap a μ) (b : Basis κ ℝ 𝔤) {ι : N → Module.Dual ℝ 𝔤}
    (hι : ContMDiff J 𝓘(ℝ, κ → ℝ) ∞ (fun m i ↦ ι m (b i))) :
    ContMDiff (I.prod J) 𝓘(ℝ, κ → ℝ) ∞ (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) :=
  ((h.contMDiff_components b).comp contMDiff_fst).sub
    (hι.comp contMDiff_snd)

/-- The derivative of the shifting map `(x, n) ↦ μ(x) - ι(n)`, read in a basis `b` of `𝔤`, is the
difference of the derivatives of its two terms. -/
theorem mfderiv_sub_apply (h : σ.IsMomentMap a μ) (b : Basis κ ℝ 𝔤)
    {ι : N → Module.Dual ℝ 𝔤} {x : M} {n : N}
    (hι : MDifferentiableAt J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n)
    (v : TangentSpace I x) (w : TangentSpace J n) (i : κ) :
    mfderiv (I.prod J) 𝓘(ℝ, κ → ℝ) (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) (x, n)
        (v, w) i =
      mfderiv I 𝓘(ℝ, κ → ℝ) (fun y i ↦ μ y (b i)) x v i -
        mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n w i := by
  have hΨ := ((h.mdifferentiableAt_components b x).hasMFDerivAt.comp (x, n)
    (hasMFDerivAt_fst (x, n))).sub (hι.hasMFDerivAt.comp (x, n) (hasMFDerivAt_snd (x, n)))
  -- The shifting map is by definition the difference of the two composites, the form in which
  -- `HasMFDerivAt.sub` states its derivative; that derivative is then evaluated pointwise.
  rw [show (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) =
      (fun y i ↦ μ y (b i)) ∘ Prod.fst - (fun m i ↦ ι m (b i)) ∘ Prod.snd from rfl,
    hΨ.mfderiv]
  -- `HasMFDerivAt.sub` types this derivative on `T_x M × T_n N` with values in the tangent space
  -- of `κ → ℝ`, type synonyms of `TangentSpace (I.prod J) (x, n)` and `κ → ℝ`. So `sub_apply`,
  -- `ContinuousLinearMap.fst` and `Pi.sub_apply` do not match syntactically (`rw` finds no
  -- type-correct motive, and the synonym has no `IsSubApply` instance): evaluate by unfolding.
  rfl

/-- **The shifting map is regular where the moment map is.** Let `ι : N → 𝔤*` have
differentiable components at `n`. Where `dμ_x` is surjective, the shifting map
`(x, n) ↦ μ(x) - ι(n)`, read in a basis of `𝔤`, has a regular point at `(x, n)`: its derivative
already sends `(v, 0)` to `dμ_x(v)`. -/
theorem isRegularPoint_sub_of_surjective (h : σ.IsMomentMap a μ) (b : Basis κ ℝ 𝔤)
    {ι : N → Module.Dual ℝ 𝔤} {x : M} {n : N}
    (hι : MDifferentiableAt J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n)
    (hx : Function.Surjective (h.differential x)) :
    IsRegularPoint (I.prod J) 𝓘(ℝ, κ → ℝ)
      (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) (x, n) := by
  classical
  rw [isRegularPoint_iff]
  intro y
  obtain ⟨v, hv⟩ := hx (b.dualBasis.equivFun.symm y)
  refine ⟨(v, 0), funext fun i ↦ (h.mfderiv_sub_apply b hι v 0 i).trans ?_⟩
  -- The `ι`-term vanishes on the zero vector of `T_n N`, read as the zero of `κ → ℝ`.
  rw [sub_eq_self.2 (by rw [map_zero]; exact Pi.zero_apply i), h.mfderiv_components_apply, hv,
    ← Basis.dualBasis_equivFun]
  exact congrFun (b.dualBasis.equivFun.apply_symm_apply _) i

/-- The image under the first projection of the kernel of the derivative of the shifting map. At
a point `(x, n)` of its zero level, if the tangent image of `ι` at `n` consists of the coordinates
of the tangent space `𝔤 · ι(n)` of the coadjoint orbit, then the first components of the kernel
vectors of the derivative of the shifting map are the vectors that `dμ_x` sends into
`𝔤 · μ(x)`. -/
private theorem exists_mem_ker_mfderiv_sub_iff (h : σ.IsMomentMap a μ) (b : Basis κ ℝ 𝔤)
    {ι : N → Module.Dual ℝ 𝔤} {x : M} {n : N}
    (hι : MDifferentiableAt J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) (hxn : μ x = ι n)
    (hιT : Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) =
      Set.range fun Z : 𝔤 ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i))
    (v : TangentSpace I x) :
    (∃ w : TangentSpace J n, ∀ i, mfderiv (I.prod J) 𝓘(ℝ, κ → ℝ)
        (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) (x, n) (v, w) i = 0) ↔
      v ∈ (LinearMap.range (μ x).coadjointTangentMap).comap (h.differential x) := by
  simp only [h.mfderiv_sub_apply b hι, sub_eq_zero, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨Z, hZ⟩ : mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n w ∈
        Set.range fun Z : 𝔤 ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i) :=
      hιT ▸ Set.mem_range_self w
    refine ⟨Submodule.Quotient.mk Z, b.ext fun i ↦ ?_⟩
    have hi := (hw i).trans (congrFun hZ i).symm
    rw [h.mfderiv_components_apply] at hi
    rw [Module.Dual.coadjointTangentMap_mk, hxn, hi]
  · rintro ⟨u, hu⟩
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨w, hw⟩ : (fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i)) ∈
        Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) :=
      hιT ▸ Set.mem_range_self Z
    refine ⟨w, fun i ↦ ?_⟩
    rw [h.mfderiv_components_apply, ← hu, Module.Dual.coadjointTangentMap_mk, hxn, hw]

end IsMomentMap

/-! ### The zero level of the shifting map -/

namespace IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {J : ModelWithCorners ℝ E'' H''} {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
  [CompleteSpace E] [CompleteSpace E']
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {κ : Type*} [Fintype κ] {c : Module.Dual ℝ (GroupLieAlgebra I G)}
  {ι : N → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

/-- **Zero is a regular value of the shifting map.** For a coadjoint-equivariant moment map of a
Lie group action, let `c` be a regular value of `μ`, and let `ι : N → 𝔤*` take values in the
coadjoint orbit of `c`, with differentiable components. Then zero is a regular value of the shifting
map `(x, n) ↦ μ(x) - ι(n)`, read in a basis of `𝔤`. -/
theorem isRegularValue_sub (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ y, μ y = c → Function.Surjective (h.toIsMomentMap.differential y))
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    (hι : ∀ n, MDifferentiableAt J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n)
    (hιc : ∀ n, ∃ g : G, ι n = Lie.coadjointRepresentation ℝ I G g c) :
    IsRegularValue (I'.prod J) 𝓘(ℝ, κ → ℝ)
      (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) 0 := by
  refine isRegularValue_iff.2 fun p hp ↦ ?_
  obtain ⟨g, hg⟩ := hιc p.2
  exact h.toIsMomentMap.isRegularPoint_sub_of_surjective b (hι p.2)
    (h.differential_surjective_of_apply_eq hreg
      ((b.ext fun i ↦ sub_eq_zero.1 (congrFun hp i)).trans hg))

variable [I'.Boundaryless] [J.Boundaryless] [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E'']
  [IsManifold J ∞ N]

/-- **The tangent image of the zero level of the shifting map.** For a coadjoint-equivariant moment
map of a Lie group action, let `c` be a regular value of `μ`, and let `ι : N → 𝔤*` be a smooth map
into the coadjoint orbit of `c` whose tangent image at each `n` consists of the coordinates of the
tangent space `𝔤 · ι(n)` of the orbit. Give the zero level of the shifting map
`(x, n) ↦ μ(x) - ι(n)`, read in a basis of `𝔤`, its regular-fibre manifold structure. Then the
projection `(x, n) ↦ x` of this zero level to `M` has tangent image `dμ_x⁻¹(𝔤 · μ(x))` at
`(x, n)`. -/
theorem range_mfderiv_fst_sub (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ y, μ y = c → Function.Surjective (h.toIsMomentMap.differential y))
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    (hιs : ContMDiff J 𝓘(ℝ, κ → ℝ) ∞ (fun m i ↦ ι m (b i)))
    (hιc : ∀ n, ∃ g : G, ι n = Lie.coadjointRepresentation ℝ I G g c)
    (hιT : ∀ n, Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) =
      Set.range fun Z : GroupLieAlgebra I G ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ _) (b i)) :
    letI := regularFiberChartedSpace (by simp) (h.toIsMomentMap.contMDiff_sub b hιs)
      BoundarylessManifold.isInteriorPoint
      (h.isRegularValue_sub hreg b (fun n ↦ (hιs n).mdifferentiableAt (by simp)) hιc)
    ∀ z : {p : M × N // (fun i ↦ μ p.1 (b i) - ι p.2 (b i)) = 0},
      LinearMap.range (mfderiv 𝓘(ℝ, Fin (finrank ℝ (E' × E'') - finrank ℝ (κ → ℝ)) → ℝ) I'
          (fun z : {p : M × N // (fun i ↦ μ p.1 (b i) - ι p.2 (b i)) = 0} ↦ z.val.1)
          z).toLinearMap =
        (LinearMap.range (μ z.val.1).coadjointTangentMap).comap
          (h.toIsMomentMap.differential z.val.1) := by
  have hΨ := h.toIsMomentMap.contMDiff_sub b hιs
  have hι : ∀ n, MDifferentiableAt J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n :=
    fun n ↦ (hιs n).mdifferentiableAt (by simp)
  have hregΨ := h.isRegularValue_sub hreg b hι hιc
  let := regularFiberChartedSpace (by simp) hΨ BoundarylessManifold.isInteriorPoint hregΨ
  have := isManifold_regularFiber (by simp) hΨ BoundarylessManifold.isInteriorPoint hregΨ
  have hemb := isSmoothEmbedding_coe_regularFiber (by simp) hΨ BoundarylessManifold.isInteriorPoint
    hregΨ
  have hker := range_mfderiv_coe_regularFiber (by simp) hΨ BoundarylessManifold.isInteriorPoint
    hregΨ
  intro z
  have hxn : μ z.val.1 = ι z.val.2 := b.ext fun i ↦ sub_eq_zero.1 (congrFun z.property i)
  have hval : MDifferentiableAt 𝓘(ℝ, Fin (finrank ℝ (E' × E'') - finrank ℝ (κ → ℝ)) → ℝ)
      (I'.prod J) Subtype.val z :=
    (hemb.contMDiff z).mdifferentiableAt (by simp)
  -- Write the projection as `Prod.fst ∘ Subtype.val` to apply the chain rule.
  rw [show (fun z : {p : M × N // (fun i ↦ μ p.1 (b i) - ι p.2 (b i)) = 0} ↦ z.val.1) =
      Prod.fst ∘ Subtype.val from rfl, mfderiv_comp z mdifferentiableAt_fst hval, mfderiv_fst]
  ext v
  rw [← h.toIsMomentMap.exists_mem_ker_mfderiv_sub_iff b (hι _) hxn (hιT _)]
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  -- The tangent image of the zero level is the kernel of the derivative of the shifting map, and
  -- membership in that kernel is the vanishing of each coordinate.
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨(mfderiv _ (I'.prod J) Subtype.val z ξ).2, ?_⟩
    have hξ : mfderiv _ (I'.prod J) Subtype.val z ξ ∈
        (mfderiv (I'.prod J) 𝓘(ℝ, κ → ℝ) _ z.val).ker := hker z ▸ LinearMap.mem_range_self _ ξ
    rw [LinearMap.mem_ker] at hξ
    exact fun i ↦ congrFun hξ i
  · rintro ⟨w, hw⟩
    have hw' : mfderiv (I'.prod J) 𝓘(ℝ, κ → ℝ)
        (fun p : M × N ↦ fun i ↦ μ p.1 (b i) - ι p.2 (b i)) z.val (v, w) = 0 := funext hw
    have hmem := LinearMap.mem_ker.2 hw'
    rw [← hker z] at hmem
    obtain ⟨ξ, hξ⟩ := hmem
    exact ⟨ξ, congrArg Prod.fst hξ⟩

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- **The zero level of the shifting map projects coisotropically to `M`.** For a nondegenerate
form and a coadjoint-equivariant moment map of a Lie group action, let `c` be a regular value of
`μ`, and let `ι : N → 𝔤*` be a smooth map into the coadjoint orbit of `c` whose tangent image at
each `n` consists of the coordinates of the tangent space `𝔤 · ι(n)` of the orbit, such as the
orbit map `G / G_c → 𝔤*`. Give the zero level of the shifting map `(x, n) ↦ μ(x) - ι(n)`, read in a
basis of `𝔤`, its regular-fibre manifold structure. Then the projection `(x, n) ↦ x` of this zero
level to `M`, whose image is the preimage `μ⁻¹(ι(N))`, is a coisotropic map. -/
theorem isCoisotropicMap_fst_sub (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate)
    (hreg : ∀ y, μ y = c → Function.Surjective (h.toIsMomentMap.differential y))
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    (hιs : ContMDiff J 𝓘(ℝ, κ → ℝ) ∞ (fun m i ↦ ι m (b i)))
    (hιc : ∀ n, ∃ g : G, ι n = Lie.coadjointRepresentation ℝ I G g c)
    (hιT : ∀ n, Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) =
      Set.range fun Z : GroupLieAlgebra I G ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ _) (b i)) :
    letI := regularFiberChartedSpace (by simp) (h.toIsMomentMap.contMDiff_sub b hιs)
      BoundarylessManifold.isInteriorPoint
      (h.isRegularValue_sub hreg b (fun n ↦ (hιs n).mdifferentiableAt (by simp)) hιc)
    hσ.IsCoisotropicMap 𝓘(ℝ, Fin (finrank ℝ (E' × E'') - finrank ℝ (κ → ℝ)) → ℝ)
      (fun z : {p : M × N // (fun i ↦ μ p.1 (b i) - ι p.2 (b i)) = 0} ↦ z.val.1) := by
  let := regularFiberChartedSpace (by simp) (h.toIsMomentMap.contMDiff_sub b hιs)
    BoundarylessManifold.isInteriorPoint
    (h.isRegularValue_sub hreg b (fun n ↦ (hιs n).mdifferentiableAt (by simp)) hιc)
  exact h.toIsMomentMap.isCoisotropicMap_of_range_mfderiv_eq hσ
    (fun z ↦ h.momentCocycle_eq_zero z.val.1) (h.range_mfderiv_fst_sub hreg b hιs hιc hιT)

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
