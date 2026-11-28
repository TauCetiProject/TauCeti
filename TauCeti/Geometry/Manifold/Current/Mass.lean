/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Current.TestForm
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.VectorBundle.Riemannian
import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.FormMetric

/-!
# Mass of currents on a Riemannian manifold

The local mass of a current on a set is the supremum of its absolute evaluations on smooth test
forms supported there with pointwise comass at most one. The pointwise norm is the operator norm
of the alternating form on the Riemannian tangent fibre, read through `TestForm.formEquiv`.
Federer's comass agrees with this norm by
`ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`. The supremum can be infinite.

As in the Euclidean theory of `Distribution.localMass`, scaling test forms gives an order-zero
bound with the local mass as optimal constant. For a continuous metric every test has bounded
comass, so local mass detects vanishing on a set. Local finiteness means that the order-zero bounds
are finite on compact sets.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
-/

public noncomputable section

open Bundle Filter Set Topology
open scoped ContDiff ENNReal Manifold NNReal

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {k : ℕ}

namespace TestForm

/-- The comass of a test form is uniformly bounded when the Riemannian metric is continuous. -/
theorem exists_bound_norm_formEquiv [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (s : TestForm I M k) : ∃ C : ℝ≥0, ∀ x, ‖formEquiv s x‖ ≤ C := by
  let α := formEquiv s
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have hα : IsSmoothForm I 0 (fun x ↦ α x) :=
    (isSmoothForm_def 0 _).2 (α.contMDiff.of_le bot_le)
  have hcont := (hα.contMDiff_alternatingFormInner hα).continuous.sqrt
  obtain ⟨C, hC⟩ := α.isCompact_tsupport.bddAbove_image hcont.continuousOn
  refine ⟨C.toNNReal, fun x ↦ ?_⟩
  by_cases hx : α x = 0
  · exact (congrArg norm hx).le.trans <|
      (norm_zero (E := TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)).le.trans C.toNNReal.property
  · exact (α x).norm_le_sqrt_alternatingFormInner_self.trans <|
      (hC (mem_image_of_mem _ (subset_closure hx))).trans (Real.le_coe_toNNReal C)

end TestForm

namespace Current

/-- The extended local mass on `U`, testing against forms of comass at most one whose closed
support lies in `U`. -/
def localMass (T : Current I M k) (U : Set M) : ℝ≥0∞ :=
  ⨆ (s : TestForm I M k) (_ : closure {x | s x ≠ 0} ⊆ U)
    (_ : ∀ x, ‖TestForm.formEquiv s x‖ ≤ 1), ‖T s‖ₑ

/-- The extended mass of a current, with tests allowed throughout the manifold. -/
def mass (T : Current I M k) : ℝ≥0∞ := localMass T univ

/-- Local mass is the supremum of evaluations in absolute value over unit-comass tests
whose closed support lies in the given set. -/
theorem localMass_def (T : Current I M k) (U : Set M) :
    localMass T U = ⨆ (s : TestForm I M k) (_ : closure {x | s x ≠ 0} ⊆ U)
      (_ : ∀ x, ‖TestForm.formEquiv s x‖ ≤ 1), ‖T s‖ₑ := (rfl)

/-- Total mass is the supremum of evaluations in absolute value over all unit-comass tests. -/
theorem mass_def (T : Current I M k) :
    mass T = ⨆ (s : TestForm I M k) (_ : ∀ x, ‖TestForm.formEquiv s x‖ ≤ 1), ‖T s‖ₑ := by
  simp only [mass, localMass_def, subset_univ, iSup_true]

variable {T S : Current I M k} {U V : Set M} {b : ℝ≥0∞}

/-- A local mass bound is exactly a bound on evaluations of the unit-comass tests in the set. -/
theorem localMass_le_iff : localMass T U ≤ b ↔ ∀ s : TestForm I M k,
    closure {x | s x ≠ 0} ⊆ U → (∀ x, ‖TestForm.formEquiv s x‖ ≤ 1) → ‖T s‖ₑ ≤ b := by
  simp only [localMass_def, iSup_le_iff]

/-- A unit-comass test supported in the set gives a lower bound for local mass. -/
theorem eNorm_apply_le_localMass {s : TestForm I M k} (hs : closure {x | s x ≠ 0} ⊆ U)
    (h₁ : ∀ x, ‖TestForm.formEquiv s x‖ ≤ 1) : ‖T s‖ₑ ≤ localMass T U :=
  localMass_le_iff.1 le_rfl s hs h₁

/-- Local mass on the whole manifold is the total mass. -/
@[simp]
theorem localMass_univ (T : Current I M k) : localMass T univ = mass T := (rfl)

/-- A mass bound is exactly a bound on evaluations of all unit-comass tests. -/
theorem mass_le_iff : mass T ≤ b ↔ ∀ s : TestForm I M k,
    (∀ x, ‖TestForm.formEquiv s x‖ ≤ 1) → ‖T s‖ₑ ≤ b := by
  simp only [mass_def, iSup_le_iff]

/-- Evaluating a unit-comass test bounds the total mass from below. -/
theorem eNorm_apply_le_mass {s : TestForm I M k}
    (h₁ : ∀ x, ‖TestForm.formEquiv s x‖ ≤ 1) : ‖T s‖ₑ ≤ mass T :=
  mass_le_iff.1 le_rfl s h₁

/-- Enlarging the set of allowed supports increases the local mass. -/
@[gcongr]
theorem localMass_mono (h : U ⊆ V) : localMass T U ≤ localMass T V :=
  localMass_le_iff.2 fun _ hs ↦ eNorm_apply_le_localMass (hs.trans h)

/-- The total mass bounds the local mass on every set. -/
theorem localMass_le_mass : localMass T U ≤ mass T :=
  localMass_mono (subset_univ U)

/-- Local mass can be recovered from masses on compact subsets, since each test has compact
support. -/
theorem localMass_eq_iSup_isCompact (T : Current I M k) (U : Set M) :
    localMass T U = ⨆ (K : Set M) (_ : IsCompact K) (_ : K ⊆ U), localMass T K := by
  refine le_antisymm (localMass_le_iff.2 fun s hs h₁ ↦ ?_)
    (iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦ localMass_mono hK)
  exact le_iSup_of_le _ <| le_iSup_of_le s.isCompact_tsupport <| le_iSup_of_le hs <|
    eNorm_apply_le_localMass Subset.rfl h₁

/-- The empty set supports only the zero test. -/
@[simp]
theorem localMass_empty (T : Current I M k) : localMass T ∅ = 0 := by
  refine le_antisymm (localMass_le_iff.2 fun s hs _ ↦ ?_) bot_le
  have hz : s = 0 := BundleTest.ext fun x ↦ by
    rw [BundleTest.zero_apply]
    exact Bundle.apply_eq_zero_of_notMem_closure fun hx ↦ hs hx
  rw [hz, map_zero, eNorm_zero]

/-- The zero current has zero local mass on every set. -/
@[simp]
theorem localMass_zero (U : Set M) : localMass (0 : Current I M k) U = 0 :=
  le_antisymm (localMass_le_iff.2 fun s _ _ ↦ by rw [zero_apply, eNorm_zero]) bot_le

/-- The zero current has zero mass. -/
@[simp]
theorem mass_zero : mass (0 : Current I M k) = 0 := localMass_zero univ

/-- Local mass is subadditive, including for currents of infinite mass. -/
theorem localMass_add_le : localMass (T + S) U ≤ localMass T U + localMass S U :=
  localMass_le_iff.2 fun s hs h₁ ↦ (eNorm_add_le (T s) (S s)).trans <| add_le_add
    (eNorm_apply_le_localMass hs h₁) (eNorm_apply_le_localMass hs h₁)

/-- The mass of a sum is bounded by the sum of the masses. -/
theorem mass_add_le : mass (T + S) ≤ mass T + mass S := localMass_add_le

/-- Local mass is homogeneous under arbitrary real scalars. -/
@[simp]
theorem localMass_smul (a : ℝ) : localMass (a • T) U = ‖a‖ₑ * localMass T U := by
  simp only [localMass, smul_apply, eNorm_smul, ENNReal.mul_iSup]

/-- Mass is homogeneous under real scalar multiplication. -/
@[simp]
theorem mass_smul (a : ℝ) : mass (a • T) = ‖a‖ₑ * mass T := localMass_smul a

/-- An integer multiplicity scales local mass by its absolute value. -/
@[simp]
theorem localMass_zsmul (m : ℤ) : localMass (m • T) U = m.natAbs * localMass T U := by
  rw [← Int.cast_smul_eq_zsmul ℝ, localMass_smul, Real.eNorm_eq_ofReal_abs, ← Int.cast_abs,
    ← Nat.cast_natAbs, ENNReal.ofReal_natCast]

/-- An integer multiplicity scales the total mass by its absolute value. -/
@[simp]
theorem mass_zsmul (m : ℤ) : mass (m • T) = m.natAbs * mass T := localMass_zsmul m

/-- Changing the sign of a current preserves its local mass. -/
@[simp]
theorem localMass_neg : localMass (-T) U = localMass T U := by
  simpa using localMass_smul (T := T) (U := U) (-1)

/-- Changing the sign of a current preserves its total mass. -/
@[simp]
theorem mass_neg : mass (-T) = mass T := localMass_neg

/-- The local mass of a difference is bounded by the sum of the local masses. -/
theorem localMass_sub_le : localMass (T - S) U ≤ localMass T U + localMass S U := by
  simpa only [sub_eq_add_neg, localMass_neg] using localMass_add_le (T := T) (S := -S) (U := U)

/-- The mass of a difference is bounded by the sum of the masses. -/
theorem mass_sub_le : mass (T - S) ≤ mass T + mass S := by
  simpa only [localMass_univ] using localMass_sub_le (T := T) (S := S) (U := univ)

/-- If a test supported in `U` has pointwise comass at most `c`, its evaluation is bounded by
`c` times the local mass, including when the local mass is infinite. -/
theorem eNorm_apply_le_localMass_mul {s : TestForm I M k} (hs : closure {x | s x ≠ 0} ⊆ U)
    {c : ℝ≥0} (hc : ∀ x, ‖TestForm.formEquiv s x‖ ≤ c) : ‖T s‖ₑ ≤ localMass T U * c := by
  obtain rfl | hc₀ := eq_zero_or_pos c
  · have hz : s = 0 := by
      apply TestForm.formEquiv.injective
      rw [TestForm.formEquiv.map_zero]
      apply BundleTest.ext
      intro x
      rw [BundleTest.zero_apply]
      exact (norm_le_zero_iff (a := TestForm.formEquiv s x)).mp (hc x)
    rw [hz, map_zero, eNorm_zero]
    exact zero_le
  have hc' : 0 < (c : ℝ) := hc₀
  have hb (x : M) : ‖TestForm.formEquiv ((c : ℝ)⁻¹ • s) x‖ ≤ 1 := by
    rw [TestForm.formEquiv.map_smul, BundleTest.smul_apply,
      norm_smul_of_nonneg (inv_nonneg.2 hc'.le) (TestForm.formEquiv s x),
      inv_mul_le_one₀ hc']
    exact hc x
  have h := eNorm_apply_le_localMass (T := T)
    ((BundleTest.tsupport_smul_subset _ s).trans hs) hb
  have heq : (c : ℝ) • ((c : ℝ)⁻¹ • s) = s := smul_inv_smul₀ hc'.ne' s
  calc
    ‖T s‖ₑ = ‖(c : ℝ)‖ₑ * ‖T ((c : ℝ)⁻¹ • s)‖ₑ := by
      rw [← eNorm_smul, ← map_smul, heq]
    _ ≤ ‖(c : ℝ)‖ₑ * localMass T U := by gcongr
    _ = localMass T U * c := by simp [mul_comm]

/-- A current has locally finite mass if each compact set admits a uniform order-zero estimate
on tests supported in it. The bound `r` applies to the Riemannian comass in every fibre. -/
def HasLocallyFiniteMass (T : Current I M k) : Prop :=
  ∀ K : Set M, IsCompact K → ∃ C : ℝ≥0, ∀ s : TestForm I M k, closure {x | s x ≠ 0} ⊆ K →
    ∀ r : ℝ≥0, (∀ x, ‖TestForm.formEquiv s x‖ ≤ r) → ‖T s‖₊ ≤ C * r

/-- Unfold local finite mass into its compact-set order-zero estimates. -/
theorem hasLocallyFiniteMass_def : HasLocallyFiniteMass T ↔
    ∀ K : Set M, IsCompact K → ∃ C : ℝ≥0, ∀ s : TestForm I M k, closure {x | s x ≠ 0} ⊆ K →
      ∀ r : ℝ≥0, (∀ x, ‖TestForm.formEquiv s x‖ ≤ r) → ‖T s‖₊ ≤ C * r := Iff.rfl

/-- The compact-set order-zero estimates are equivalent to finiteness of the variational local
mass on every compact set. -/
theorem hasLocallyFiniteMass_iff_localMass_ne_top :
    HasLocallyFiniteMass T ↔ ∀ K : Set M, IsCompact K → localMass T K ≠ ⊤ := by
  constructor
  · intro h K hK
    obtain ⟨C, hC⟩ := h K hK
    refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := C)) <| localMass_le_iff.2 fun s hs h₁ ↦ ?_
    exact_mod_cast (by simpa using hC s hs 1 h₁ : ‖T s‖₊ ≤ C)
  · intro h K hK
    refine ⟨(localMass T K).toNNReal, fun s hs r hr ↦ ?_⟩
    have hbound := eNorm_apply_le_localMass_mul (T := T) hs hr
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_mul, ENNReal.coe_toNNReal (h K hK), eNorm_eq_nnNorm] using hbound

/-- Globally finite mass implies locally finite mass. -/
theorem hasLocallyFiniteMass_of_mass_ne_top (h : mass T ≠ ⊤) : HasLocallyFiniteMass T :=
  hasLocallyFiniteMass_iff_localMass_ne_top.2 fun _ _ ↦ ne_top_of_le_ne_top h localMass_le_mass

/-- The zero current has locally finite mass. -/
@[simp]
theorem hasLocallyFiniteMass_zero : HasLocallyFiniteMass (0 : Current I M k) :=
  hasLocallyFiniteMass_of_mass_ne_top (by simp)

/-- The sum of two currents of locally finite mass has locally finite mass. -/
theorem HasLocallyFiniteMass.add (hT : HasLocallyFiniteMass T) (hS : HasLocallyFiniteMass S) :
    HasLocallyFiniteMass (T + S) := by
  refine hasLocallyFiniteMass_iff_localMass_ne_top.2 fun K hK ↦ ?_
  have hTK := hasLocallyFiniteMass_iff_localMass_ne_top.1 hT K hK
  have hSK := hasLocallyFiniteMass_iff_localMass_ne_top.1 hS K hK
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hTK, hSK⟩) localMass_add_le

/-- Changing the sign of a current preserves local finiteness of mass. -/
@[simp]
theorem hasLocallyFiniteMass_neg_iff : HasLocallyFiniteMass (-T) ↔ HasLocallyFiniteMass T := by
  simp only [hasLocallyFiniteMass_iff_localMass_ne_top, localMass_neg]

/-- The negative of a current of locally finite mass has locally finite mass. -/
theorem HasLocallyFiniteMass.neg (hT : HasLocallyFiniteMass T) : HasLocallyFiniteMass (-T) :=
  hasLocallyFiniteMass_neg_iff.2 hT

/-- The difference of two currents of locally finite mass has locally finite mass. -/
theorem HasLocallyFiniteMass.sub (hT : HasLocallyFiniteMass T) (hS : HasLocallyFiniteMass S) :
    HasLocallyFiniteMass (T - S) := by
  simpa only [sub_eq_add_neg] using hT.add hS.neg

/-- A real multiple of a current of locally finite mass has locally finite mass. -/
theorem HasLocallyFiniteMass.smul (hT : HasLocallyFiniteMass T) (a : ℝ) :
    HasLocallyFiniteMass (a • T) := by
  refine hasLocallyFiniteMass_iff_localMass_ne_top.2 fun K hK ↦ ?_
  rw [localMass_smul]
  exact ENNReal.mul_ne_top eNorm_ne_top (hasLocallyFiniteMass_iff_localMass_ne_top.1 hT K hK)

/-- An integer multiple of a current of locally finite mass has locally finite mass. -/
theorem HasLocallyFiniteMass.zsmul (hT : HasLocallyFiniteMass T) (m : ℤ) :
    HasLocallyFiniteMass (m • T) := by
  rw [← Int.cast_smul_eq_zsmul ℝ]
  exact hT.smul (m : ℝ)

/-- A current vanishing on every test supported in the set has zero local mass there. -/
theorem localMass_eq_zero_of_isVanishingOn (h : BundleTest.IsVanishingOn T U) :
    localMass T U = 0 := by
  refine le_antisymm (localMass_le_iff.2 fun s hs _ ↦ ?_) bot_le
  rw [BundleTest.isVanishingOn_iff.1 h s hs, eNorm_zero]

/-- Local mass zero detects vanishing on every test supported in the set. -/
theorem localMass_eq_zero_iff_isVanishingOn
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] :
    localMass T U = 0 ↔ BundleTest.IsVanishingOn T U := by
  constructor
  · intro h
    apply BundleTest.isVanishingOn_iff.2
    intro s hs
    obtain ⟨c, hc⟩ := TestForm.exists_bound_norm_formEquiv s
    simpa [h] using eNorm_apply_le_localMass_mul (T := T) hs hc
  · exact localMass_eq_zero_of_isVanishingOn

/-- A current has zero mass precisely when it is zero. -/
@[simp]
theorem mass_eq_zero_iff [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] :
    mass T = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ DFunLike.ext _ _ fun s ↦ BundleTest.isVanishingOn_iff.1
    (localMass_eq_zero_iff_isVanishingOn.1 h) s (subset_univ _), ?_⟩
  rintro rfl
  exact mass_zero

/-- Weak convergence on tests supported in `U` makes the local mass lower semicontinuous. -/
theorem localMass_le_liminf {ι : Type*} {l : Filter ι} {A : ι → Current I M k}
    (h : ∀ s : TestForm I M k, closure {x | s x ≠ 0} ⊆ U →
      Tendsto (fun i ↦ A i s) l (𝓝 (T s))) :
    localMass T U ≤ liminf (fun i ↦ localMass (A i) U) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  refine localMass_le_iff.2 fun s hs h₁ ↦ ?_
  exact (h s hs).eNorm.liminf_eq.ge.trans <| liminf_le_liminf <|
    .of_forall fun i ↦ eNorm_apply_le_localMass (T := A i) hs h₁

/-- Mass is lower semicontinuous for convergence against every fixed test form. -/
theorem mass_le_liminf {ι : Type*} {l : Filter ι} {A : ι → Current I M k}
    (h : ∀ s : TestForm I M k, Tendsto (fun i ↦ A i s) l (𝓝 (T s))) :
    mass T ≤ liminf (fun i ↦ mass (A i)) l :=
  localMass_le_liminf fun s _ ↦ h s

section Localization

variable [T2Space M]

/-- Every neighbourhood of the support of a current sees its full mass, even when that mass
is infinite. -/
theorem localMass_eq_mass_of_dsupport_subset_interior (hU : BundleTest.dsupport T ⊆ interior U) :
    localMass T U = mass T := by
  refine le_antisymm localMass_le_mass (mass_le_iff.2 fun s h₁ ↦ ?_)
  let K := closure {x | s x ≠ 0}
  have hc : IsCompact (K ∩ BundleTest.dsupport T) :=
    s.isCompact_tsupport.inter_right (BundleTest.isClosed_dsupport _)
  obtain ⟨ρ, hρ, hone, -, hsupp, hρ₁⟩ :=
    hc.exists_contMDiff_one_nhds_tsupport_subset I isOpen_interior (inter_subset_right.trans hU)
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨ρ, hρ⟩
  let t := BundleTest.smulLeftCLM χ s
  have hts : T s = T t := by
    apply BundleTest.map_eq_map_of_eventuallyEq T
    refine eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_
    by_cases hxs : x ∈ K
    · filter_upwards [eventually_nhdsSet_iff_forall.1 hone x ⟨hxs, hx⟩] with y hy
      have hχ : χ y = 1 := hy
      rw [BundleTest.smulLeftCLM_apply, hχ, one_smul]
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxs] with y hy
      rw [BundleTest.smulLeftCLM_apply, Bundle.apply_eq_zero_of_notMem_closure hy, smul_zero]
  rw [hts]
  refine eNorm_apply_le_localMass (s := t)
    ((BundleTest.tsupport_smulLeftCLM_subset χ s).trans
      (inter_subset_left.trans (hsupp.trans interior_subset))) fun x ↦ ?_
  have hx : TestForm.formEquiv t x = ρ x • TestForm.formEquiv s x := by
    let := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
      (E := (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
      (F := DensityBundle I M x)
    apply (I.formDensityDoubleDualEquiv k x).injective
    rw [TestForm.formDensityDoubleDualEquiv_formEquiv_apply, ContinuousLinearEquiv.map_smul,
      TestForm.formDensityDoubleDualEquiv_formEquiv_apply, BundleTest.smulLeftCLM_apply]
    rfl
  rw [hx, norm_smul_of_nonneg (hρ₁ x).1 (TestForm.formEquiv s x)]
  exact (mul_le_of_le_one_left (norm_nonneg (TestForm.formEquiv s x)) (hρ₁ x).2).trans (h₁ x)

/-- A compactly supported current has finite mass if and only if it has locally finite mass. -/
theorem hasLocallyFiniteMass_iff_mass_ne_top_of_isCompact_dsupport
    (hc : IsCompact (BundleTest.dsupport T)) : HasLocallyFiniteMass T ↔ mass T ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, hasLocallyFiniteMass_of_mass_ne_top⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨K, hK, hKint, -⟩ := exists_compact_between hc isOpen_univ (subset_univ _)
  rw [← localMass_eq_mass_of_dsupport_subset_interior hKint]
  exact hasLocallyFiniteMass_iff_localMass_ne_top.1 h K hK

end Localization

end Current

end TauCeti
