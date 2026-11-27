/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.CharacterAnnihilator
public import TauCeti.NumberTheory.LocalField.AddChar.DualLattice
public import TauCeti.NumberTheory.LocalField.Lattice
public import TauCeti.Topology.LocallyConstant.CompactSupport
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Fourier.FinsetSum
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.Topology.Algebra.AddChar

/-!
# The Fourier transform of Schwartz–Bruhat functions over a nonarchimedean local field

Let `K` be a nonarchimedean local field with valuation ring `O = 𝒪[K]`, `V` a finite-dimensional
`K`-vector space with its module topology, `B` a bilinear form on `V`, `ψ` a continuous additive
character of `K` with values in the unit circle, and `μ` a translation invariant measure on `V`.
Write `𝓕 f (w) = ∫ ψ (-B v w) • f v ∂μ` for `VectorFourier.fourierIntegral ψ μ B f`. The local
Schwartz–Bruhat space `S(V)` is the space `C_c^∞(V, E) = LocallyConstant.compactlySupported ℂ V E`
of locally constant compactly supported functions on `V`. This file proves that `𝓕` maps `S(V)` to
itself, for every nontrivial `ψ`, every nondegenerate `B` and every such `μ`, and computes the
transform `𝓕'` for the transposed form `B.flip` and a second measure `ν` after `𝓕`:
`𝓕' (𝓕 f) (x) = (μ(M) ν(M^∨)) • f (-x)` for any lattice `M` of periods of `f`, where `M^∨` is the
annihilator of `M` for `ψ (B x y)`. No normalization of `μ`, `ν` or `ψ` is assumed. When
`μ(L) ν(L^∨) = 1` for every lattice `L`, as for the self-dual Haar measure `μ = ν` of `ψ` and `B`,
this is Fourier inversion `𝓕' (𝓕 f) (x) = f (-x)`, and `𝓕` is then a linear bijection of `S(V)`.
For a symmetric form `B.flip = B`, so that `𝓕' = 𝓕` when `ν = μ`.

The proofs rest on the lattices of `V` (finitely generated `O`-submodules spanning `V`), which are
compact open subgroups. Every compact set lies in a lattice and every neighbourhood of `0` contains
one (`TauCeti.NumberTheory.LocalField.Lattice`), so a locally constant compactly supported
function is supported in a lattice and is invariant under translation by another. The Fourier
identities for character annihilators in `TauCeti.Analysis.Fourier.CharacterAnnihilator` then give
local constancy (from the support lattice) and compact support (from the lattice of periods, whose
annihilator is a lattice by `Submodule.isFullLattice_characterAnnihilator`). For inversion, a
function with a lattice `M` of periods and compact support is a finite combination of indicators
of cosets of `M`, and on each of these the two transforms are computed by the subgroup indicator
formula and the double duality `Submodule.characterAnnihilator_characterAnnihilator_flip`.

## Main definitions

* `LocallyConstant.compactlySupportedFourier`: the Fourier transform as a `ℂ`-linear endomorphism
  of `C_c^∞(V, E)`.

## Main results

* `VectorFourier.isLocallyConstant_fourierIntegral_of_hasCompactSupport`: the Fourier transform of
  a compactly supported function is locally constant.
* `VectorFourier.hasCompactSupport_fourierIntegral_of_isLocallyConstant`: for `ψ` nontrivial and
  `B` nondegenerate, the Fourier transform of a locally constant compactly supported function has
  compact support.
* `VectorFourier.fourierIntegral_fourierIntegral_eq_smul_of_periodic`: the double transform of a
  compactly supported function with a lattice `M` of periods is `x ↦ (μ(M) ν(M^∨)) • f (-x)`, for
  any pair of measures; `VectorFourier.fourierIntegral_fourierIntegral_of_periodic` is the
  inversion formula for an arbitrary subgroup of periods when the volume factor is `1`.
* `VectorFourier.fourierIntegral_fourierIntegral_of_isLocallyConstant`,
  `VectorFourier.fourierIntegral_flip_fourierIntegral_of_isLocallyConstant`: Fourier inversion on
  `S(V)`, in both orders, for measures with `μ(L) ν(L^∨) = 1` for every lattice `L`.
* `LocallyConstant.compactlySupportedFourier_bijective`: for such a measure `μ = ν`, the transform
  is a bijection of `C_c^∞(V, E)`.
* `VectorFourier.fourierIntegral_neg_mul_apply`,
  `VectorFourier.integral_mul_fourierIntegral_mul_comm`: on `V = K` with the form `-(x y)`, the
  transform has the positive kernel `ψ(x y)`, and `∫ f 𝓕g(· t) = ∫ g 𝓕f(· t)`.
* `VectorFourier.isLocallyConstant_hasCompactSupport_fourierIntegral_neg_mul`,
  `VectorFourier.fourierIntegral_neg_mul_indicator_integer`: on `V = K`, the transform with the
  positive kernel maps `S(K)` to itself, and fixes `1_𝒪` when `ψ` has conductor exponent `0` and
  `μ(𝒪[K]) = 1`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter VII, §2.
-/

public section

open Filter Topology ValuativeRel MeasureTheory Function Set
open scoped Pointwise

/-! ### The transform with the positive kernel `ψ(x y)` on a field -/

section NegMul

variable {K : Type*} [Field K]

/-- The form `-(x y)` on a field is nondegenerate; it is the form for which Mathlib's
`VectorFourier.fourierIntegral` has the positive kernel `ψ(x y)`. -/
theorem LinearMap.BilinForm.nondegenerate_neg_mul :
    (-LinearMap.mul K K : LinearMap.BilinForm K K).Nondegenerate :=
  ⟨fun x hx ↦ by simpa using hx 1, fun y hy ↦ by simpa using hy 1⟩

namespace VectorFourier

/-- With the form `-(x y)`, the Fourier transform has the positive kernel:
`𝓕 f (y) = ∫ ψ(x y) f(x) dμ(x)`. -/
theorem fourierIntegral_neg_mul_apply [MeasurableSpace K] (ψ : AddChar K Circle) (μ : Measure K)
    (f : K → ℂ) (y : K) :
    fourierIntegral ψ μ (-LinearMap.mul K K) f y = ∫ x, (ψ (x * y) : ℂ) * f x ∂μ := by
  simp [fourierIntegral, Circle.smul_def]

/-- **Symmetry of the Fourier pairing.** For the transform with kernel `ψ(x y)`, integrable `f`,
`g` and every `t`, `∫ f(x) 𝓕g(x t) dμ(x) = ∫ g(x) 𝓕f(x t) dμ(x)`: both are
`∫∫ f(x) g(y) ψ(x y t)`. -/
theorem integral_mul_fourierIntegral_mul_comm [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle}
    (hψ : Continuous ψ) (μ : Measure K) [SFinite μ] {f g : K → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) (t : K) :
    ∫ x, f x * fourierIntegral ψ μ (-LinearMap.mul K K) g (x * t) ∂μ =
      ∫ x, g x * fourierIntegral ψ μ (-LinearMap.mul K K) f (x * t) ∂μ := by
  simp_rw [fourierIntegral_neg_mul_apply, ← integral_const_mul]
  have hk : Continuous fun z : K × K ↦ (ψ (z.2 * (z.1 * t)) : ℂ) :=
    continuous_subtypeVal.comp
      (hψ.comp (continuous_snd.mul (continuous_fst.mul continuous_const)))
  have hm : AEStronglyMeasurable (fun z : K × K ↦ f z.1 * ((ψ (z.2 * (z.1 * t)) : ℂ) * g z.2))
      (μ.prod μ) :=
    hf.1.comp_fst.mul (hk.aestronglyMeasurable.mul hg.1.comp_snd)
  have hint : Integrable (fun z : K × K ↦ f z.1 * ((ψ (z.2 * (z.1 * t)) : ℂ) * g z.2))
      (μ.prod μ) :=
    (hf.norm.mul_prod hg.norm).mono' hm (ae_of_all _ fun z ↦ by simp)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y ↦ integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  simp only
  rw [show y * (x * t) = x * (y * t) by ring]
  ring

end VectorFourier

end NegMul

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [AddCommGroup V] [Module K V] [Module 𝒪[K] V] [IsScalarTower 𝒪[K] K V]
  [FiniteDimensional K V] [TopologicalSpace V] [IsModuleTopology K V]

namespace VectorFourier

variable [MeasurableSpace V] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {ψ : AddChar K Circle} {B : LinearMap.BilinForm K V}

/-- **Local constancy of the transform.** For a continuous `ψ`, the Fourier transform of a
compactly supported function on `V` is locally constant, for every measure `μ` and every bilinear
form `B`. -/
theorem isLocallyConstant_fourierIntegral_of_hasCompactSupport (hψ : Continuous ψ)
    (μ : Measure V) (B : LinearMap.BilinForm K V) {f : V → E} (hf : HasCompactSupport f) :
    IsLocallyConstant (fourierIntegral ψ μ B f) := by
  -- The support lies in a compact lattice, whose annihilator is open.
  obtain ⟨L, hL, hfL⟩ := Submodule.exists_isFullLattice_superset_of_isCompact (E := K)
    hf.isCompact
  exact isLocallyConstant_fourierIntegral ψ μ B (U := L.toAddSubgroup)
    (Submodule.IsFullLattice.isCompact L)
    (hψ.comp (IsModuleTopology.continuous_bilinear_of_finite_left B))
    ((subset_tsupport f).trans hfL)

variable [BorelSpace V]

/-- **Compact support of the transform.** For a continuous nontrivial `ψ`, a nondegenerate `B` and
a translation invariant measure `μ`, the Fourier transform of a locally constant compactly
supported function on `V` has compact support. -/
theorem hasCompactSupport_fourierIntegral_of_isLocallyConstant (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddRightInvariant] {f : V → E}
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    HasCompactSupport (fourierIntegral ψ μ B f) := by
  have : T2Space V := TauCeti.ModuleTopology.t2Space (Module.finBasis K V)
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  -- `𝓕 f` is supported in the annihilator of a lattice of periods, which is again a lattice.
  obtain ⟨M, hM, hper⟩ := Submodule.exists_isFullLattice_forall_periodic (E := K) hf hfc
  have hA := Submodule.isFullLattice_characterAnnihilator
    (AddChar.setOf_eq_one_mem_nhds_zero hψ) h1 hB M
  refine hasCompactSupport_fourierIntegral ψ μ B (U := M.toAddSubgroup) hper ?_
  rw [← Submodule.toAddSubgroup_characterAnnihilator]
  exact Submodule.IsFullLattice.isCompact _

section Inversion

variable [CompleteSpace E]

omit [FiniteDimensional K V] in
/-- **Inversion for a coset indicator.** Transforming `1_(a + M) • c` for `(μ, B)` and then for
`(ν, B.flip)` gives `x ↦ 1_(a + M)(-x) • (μ(M) ν(M^∨)) • c`. -/
private theorem fourierIntegral_fourierIntegral_indicator_sub (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ ν : Measure V) [μ.IsAddRightInvariant] [ν.IsAddRightInvariant]
    (M : Submodule 𝒪[K] V) [M.IsFullLattice K] (c : E) (a : V) :
    fourierIntegral ψ ν B.flip
        (fourierIntegral ψ μ B fun v ↦ (M : Set V).indicator (fun _ ↦ c) (v - a)) =
      fun x ↦ (M : Set V).indicator
        (fun _ ↦ (μ.real M * ν.real (M.characterAnnihilator ψ B)) • c) (-x - a) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  have h0 := AddChar.setOf_eq_one_mem_nhds_zero hψ
  have hA := Submodule.isFullLattice_characterAnnihilator h0 h1 hB M
  have h₁ := fourierIntegral_indicator_addSubgroup_comp_sub_right ψ μ B (U := M.toAddSubgroup)
    (Submodule.IsFullLattice.isOpen M).measurableSet c a
  -- The phase `ψ (-B a w)` is the modulation by `ψ (B.flip w (-a))`.
  have hphase (w : V) : ψ (-B a w) = ψ (B.flip w (-a)) := by simp
  simp only [← Submodule.toAddSubgroup_characterAnnihilator, Submodule.coe_toAddSubgroup,
    hphase] at h₁
  rw [h₁, fourierIntegral_char_smul]
  ext x
  have h := congrFun (fourierIntegral_indicator_addSubgroup ψ ν B.flip
    (U := (M.characterAnnihilator ψ B).toAddSubgroup)
    (Submodule.IsFullLattice.isOpen _).measurableSet (μ.real (M : Set V) • c)) (x - -a)
  rw [← Submodule.toAddSubgroup_characterAnnihilator,
    Submodule.characterAnnihilator_characterAnnihilator_flip h0 h1 hB M] at h
  simp only [Submodule.coe_toAddSubgroup] at h
  rw [h, smul_smul, mul_comm, sub_neg_eq_add]
  -- `x + a ∈ M` exactly when `-x - a = -(x + a) ∈ M`.
  classical
  rw [show -x - a = -(x + a) by abel]
  simp only [Set.indicator_apply, SetLike.mem_coe, neg_mem_iff]

/-- **Double Fourier transform.** Let `μ` and `ν` be translation invariant measures on `V`,
finite on compact sets, and let `f` be a compactly supported function invariant under translation
by a lattice `M`. Transforming `f` for `(μ, B)` and then for `(ν, B.flip)` gives
`x ↦ (μ(M) ν(M^∨)) • f (-x)`, where `M^∨ = M.characterAnnihilator ψ B`. The factor is `1` for
the self-dual measure, giving Fourier inversion. -/
theorem fourierIntegral_fourierIntegral_eq_smul_of_periodic (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ ν : Measure V) [μ.IsAddRightInvariant] [ν.IsAddRightInvariant]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (M : Submodule 𝒪[K] V)
    [M.IsFullLattice K] {f : V → E} (hper : ∀ u ∈ M, Periodic f u) (hfc : HasCompactSupport f) :
    fourierIntegral ψ ν B.flip (fourierIntegral ψ μ B f) =
      fun x ↦ (μ.real M * ν.real (M.characterAnnihilator ψ B)) • f (-x) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  obtain ⟨s, hs⟩ := Submodule.exists_eq_sum_indicator_sub M hper hfc
  set g : V → V → E := fun a v ↦ (M : Set V).indicator (fun _ ↦ f a) (v - a)
  have hfg : f = ∑ a ∈ s, g a := funext fun x ↦ by simp [g, hs x]
  -- Each coset indicator is locally constant with compact support, so it and its first
  -- transform are integrable.
  have hg (a : V) : IsLocallyConstant (g a) ∧ HasCompactSupport (g a) :=
    ⟨(LocallyConstant.indicator (LocallyConstant.const V (f a))
        ⟨Submodule.IsFullLattice.isClosed M, Submodule.IsFullLattice.isOpen M⟩).isLocallyConstant
        |>.comp_continuous (continuous_sub_right a),
      (HasCompactSupport.intro (f := (M : Set V).indicator fun _ ↦ f a)
        (Submodule.IsFullLattice.isCompact M) fun _ hx ↦
        indicator_of_notMem hx _).comp_homeomorph (Homeomorph.subRight a)⟩
  have hint (a : V) : Integrable (fourierIntegral ψ μ B (g a)) ν :=
    (isLocallyConstant_fourierIntegral_of_hasCompactSupport hψ μ B (hg a).2).continuous
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_fourierIntegral_of_isLocallyConstant hψ h1 hB μ (hg a).1 (hg a).2)
  rw [hfg, fourierIntegral_finsetSum hψ (IsModuleTopology.continuous_bilinear_of_finite_left B) s
      fun a _ ↦ (hg a).1.continuous.integrable_of_hasCompactSupport (hg a).2,
    fourierIntegral_finsetSum hψ (IsModuleTopology.continuous_bilinear_of_finite_left B.flip) s
      fun a _ ↦ hint a]
  ext x
  rw [Finset.sum_apply, Finset.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  dsimp only [g]
  rw [fourierIntegral_fourierIntegral_indicator_sub hψ h1 hB μ ν M]
  exact Set.indicator_const_smul_apply _ _ _ _

/-- **Fourier inversion on `S(V)`.** If `μ(L) ν(L^∨) = 1` for every lattice `L` of `V`, as for
the self-dual Haar measure `μ = ν` of `ψ` and `B`, then for every locally constant compactly
supported `f` the transform for `(ν, B.flip)` of the transform of `f` for `(μ, B)` is
`x ↦ f (-x)`. -/
theorem fourierIntegral_fourierIntegral_of_isLocallyConstant (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ ν : Measure V) [μ.IsAddRightInvariant] [ν.IsAddRightInvariant]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hvol : ∀ L : Submodule 𝒪[K] V, L.IsFullLattice K →
      μ.real L * ν.real (L.characterAnnihilator ψ B) = 1)
    {f : V → E} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    fourierIntegral ψ ν B.flip (fourierIntegral ψ μ B f) = fun x ↦ f (-x) := by
  obtain ⟨M, hM, hper⟩ := Submodule.exists_isFullLattice_forall_periodic (E := K) hf hfc
  rw [fourierIntegral_fourierIntegral_eq_smul_of_periodic hψ h1 hB μ ν M hper hfc, hvol M hM]
  simp

/-- **Fourier inversion in the other order.** Under the same volume condition
`μ(L) ν(L^∨) = 1` for every lattice `L`, transforming a locally constant compactly supported `g`
first for `(ν, B.flip)` and then for `(μ, B)` also gives `x ↦ g (-x)`. -/
theorem fourierIntegral_flip_fourierIntegral_of_isLocallyConstant (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) (hB : B.Nondegenerate) (μ ν : Measure V) [μ.IsAddRightInvariant]
    [ν.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hvol : ∀ L : Submodule 𝒪[K] V, L.IsFullLattice K →
      μ.real L * ν.real (L.characterAnnihilator ψ B) = 1)
    {g : V → E} (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) :
    fourierIntegral ψ μ B (fourierIntegral ψ ν B.flip g) = fun x ↦ g (-x) := by
  -- Every lattice is the annihilator of its annihilator for `B.flip`, so the volume condition
  -- for `(μ, ν, B)` is the condition for `(ν, μ, B.flip)`.
  have h0 := AddChar.setOf_eq_one_mem_nhds_zero hψ
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have h := fourierIntegral_fourierIntegral_of_isLocallyConstant hψ h1 hB.flip ν μ
    (fun L hL ↦ ?_) hg hgc
  · rwa [hflip] at h
  -- `L` is the annihilator of `L' = L.characterAnnihilator ψ B.flip`.
  have hL' := Submodule.isFullLattice_characterAnnihilator h0 h1 hB.flip L
  have hdd := Submodule.characterAnnihilator_characterAnnihilator_flip h0 h1 hB.flip L
  rw [hflip] at hdd
  rw [mul_comm, ← hvol _ hL', hdd]

end Inversion

end VectorFourier

/-! ### The positive kernel on a local field -/

namespace VectorFourier

variable [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle} (μ : Measure K)
  [μ.IsAddRightInvariant]

/-- For a continuous nontrivial `ψ`, the transform `f ↦ ∫ ψ(x y) f(x) dμ(x)` maps a locally
constant compactly supported function on `K` to another one. -/
theorem isLocallyConstant_hasCompactSupport_fourierIntegral_neg_mul (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {g : K → ℂ} (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) :
    IsLocallyConstant (fourierIntegral ψ μ (-LinearMap.mul K K) g) ∧
      HasCompactSupport (fourierIntegral ψ μ (-LinearMap.mul K K) g) :=
  ⟨isLocallyConstant_fourierIntegral_of_hasCompactSupport hψ μ _ hgc,
    hasCompactSupport_fourierIntegral_of_isLocallyConstant hψ h1
      LinearMap.BilinForm.nondegenerate_neg_mul μ hg hgc⟩

/-- For `ψ` of conductor exponent `0` and `μ(𝒪[K]) = 1`, the transform
`f ↦ ∫ ψ(x y) f(x) dμ(x)` of `1_𝒪` is `1_𝒪`: the annihilator of `𝒪[K]` for `ψ(x y)` is
`𝒪[K]`. -/
theorem fourierIntegral_neg_mul_indicator_integer (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hψ0 : ψ.conductorExponent = 0) (hμ : μ 𝒪[K] = 1) :
    fourierIntegral ψ μ (-LinearMap.mul K K) ((𝒪[K] : Set K).indicator (1 : K → ℂ)) =
      (𝒪[K] : Set K).indicator 1 := by
  have h0 := AddChar.setOf_eq_one_mem_nhds_zero hψ
  have hO : MeasurableSet ((𝒪[K]).toAddSubgroup : Set K) :=
    (Valuation.isClopen_integer (v := valuation K)).isClosed.measurableSet
  have hann : (((𝒪[K]).toAddSubgroup.characterAnnihilator ψ (-LinearMap.mul K K)) : Set K) =
      𝒪[K] := by
    ext y
    have key := AddChar.forall_mul_eq_one_iff_valuation_le h0 h1 0 y
    rw [hψ0, neg_zero, sub_zero, zpow_zero] at key
    rw [SetLike.mem_coe, AddSubgroup.mem_characterAnnihilator, SetLike.mem_coe,
      Valuation.mem_integer_iff, ← key]
    -- `𝒪[K]` is stable under negation, and `ψ (-(x y))` is `ψ ((-x) y)`.
    refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
    · have hx' : -x ∈ (𝒪[K]).toAddSubgroup := neg_mem (show x ∈ 𝒪[K] from
        (Valuation.mem_integer_iff _ _).2 hx)
      simpa using h _ hx'
    · have hx' : valuation K (-x) ≤ uniformizer K ^ (0 : ℤ) := by
        rw [Valuation.map_neg, zpow_zero]
        exact (Valuation.mem_integer_iff _ _).1 hx
      simpa using h _ hx'
  have h := fourierIntegral_indicator_addSubgroup ψ μ (-LinearMap.mul K K) hO
    (1 : ℂ)
  rw [hann, measureReal_def] at h
  simp only [Pi.one_def]
  simpa [hμ] using h

end VectorFourier

namespace LocallyConstant

open VectorFourier

variable [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {ψ : AddChar K Circle} {B : LinearMap.BilinForm K V}

/-- **The Fourier transform on `S(V)`.** For a continuous nontrivial `ψ`, a nondegenerate `B` and
a translation invariant measure `μ` finite on compact sets, the Fourier transform
`f ↦ (w ↦ ∫ ψ (-B v w) • f v ∂μ)` as a `ℂ`-linear endomorphism of the space
`C_c^∞(V, E) = LocallyConstant.compactlySupported ℂ V E` of locally constant compactly supported
functions. -/
noncomputable def compactlySupportedFourier (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] :
    compactlySupported ℂ V E →ₗ[ℂ] compactlySupported ℂ V E where
  toFun f := ⟨⟨fourierIntegral ψ μ B f,
      isLocallyConstant_fourierIntegral_of_hasCompactSupport hψ μ B
        (mem_compactlySupported.1 f.property)⟩,
    mem_compactlySupported.2 <| hasCompactSupport_fourierIntegral_of_isLocallyConstant hψ h1 hB μ
      (LocallyConstant.isLocallyConstant _) (mem_compactlySupported.1 f.property)⟩
  map_add' f g := by
    refine compactlySupported.coeFn_injective ?_
    have hint (h : compactlySupported ℂ V E) : Integrable (h : V → E) μ :=
      (h : LocallyConstant V E).continuous.integrable_of_hasCompactSupport
        (mem_compactlySupported.1 h.property)
    exact fourierIntegral_add hψ (IsModuleTopology.continuous_bilinear_of_finite_left B)
      (hint f) (hint g)
  map_smul' c f := compactlySupported.coeFn_injective (fourierIntegral_const_smul _ _ _ _ c)

@[simp]
theorem coe_compactlySupportedFourier_apply (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (f : compactlySupported ℂ V E) :
    ((compactlySupportedFourier hψ h1 hB μ f : LocallyConstant V E) : V → E) =
      fourierIntegral ψ μ B f :=
  (rfl)

/-- **The Fourier transform is a bijection of `S(V)`** for a measure `μ` with `μ(L) μ(L^∨) = 1`
for every lattice `L`, that is, for the self-dual measure of `ψ` and `B`. Its inverse is the
transform for `B.flip` followed by `x ↦ -x`. -/
theorem compactlySupportedFourier_bijective [CompleteSpace E] (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (hvol : ∀ L : Submodule 𝒪[K] V, L.IsFullLattice K →
      μ.real L * μ.real (L.characterAnnihilator ψ B) = 1) :
    Bijective (compactlySupportedFourier (E := E) hψ h1 hB μ) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  -- The transform for `B.flip` undoes `compactlySupportedFourier` up to `x ↦ -x`.
  have hinv (f : compactlySupported ℂ V E) (x : V) :
      fourierIntegral ψ μ B.flip (fourierIntegral ψ μ B ((f : LocallyConstant V E) : V → E)) (-x) =
        (f : LocallyConstant V E) x := by
    simpa using congrFun (fourierIntegral_fourierIntegral_of_isLocallyConstant
      (f := ((f : LocallyConstant V E) : V → E)) hψ h1 hB μ μ hvol
      (LocallyConstant.isLocallyConstant _) (mem_compactlySupported.1 f.property)) (-x)
  refine ⟨fun f g hfg ↦ compactlySupported.coeFn_injective (funext fun x ↦ ?_), fun g ↦ ?_⟩
  · have h := congrArg (fun h : compactlySupported ℂ V E ↦
      fourierIntegral ψ μ B.flip ((h : LocallyConstant V E) : V → E) (-x)) hfg
    simp only [coe_compactlySupportedFourier_apply] at h
    exact (hinv f x).symm.trans (h.trans (hinv g x))
  · -- The preimage of `g` is the transform for `B.flip` of `x ↦ g (-x)`.
    let g₀ : V → E := fun x ↦ (g : LocallyConstant V E) (-x)
    have hg₀ : IsLocallyConstant g₀ :=
      (LocallyConstant.isLocallyConstant _).comp_continuous continuous_neg
    have hg₀c : HasCompactSupport g₀ :=
      (mem_compactlySupported.1 g.property).comp_homeomorph (Homeomorph.neg V)
    refine ⟨⟨⟨fourierIntegral ψ μ B.flip g₀,
      isLocallyConstant_fourierIntegral_of_hasCompactSupport hψ μ B.flip hg₀c⟩,
      mem_compactlySupported.2 (hasCompactSupport_fourierIntegral_of_isLocallyConstant hψ h1
        hB.flip μ hg₀ hg₀c)⟩, compactlySupported.coeFn_injective ?_⟩
    simpa [g₀] using fourierIntegral_flip_fourierIntegral_of_isLocallyConstant hψ h1 hB μ μ hvol
      hg₀ hg₀c

end LocallyConstant
