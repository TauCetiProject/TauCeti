/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.NumberTheory.LocalField.Discriminant.Integral
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.FieldTheory.Galois.SubfieldDictionary

/-!
# The slope polygon of a finite separable local-field extension

For a finite separable extension `L/K` of a nonarchimedean local field `K`, taking at each degree
`n : ℕ` the infimum of `δ(E/K)` over intermediate fields `E` with `[E : K] = n` and taking the
lower convex envelope defines `TauCeti.slopePolygon K L : ℕ → WithTop ℝ`. Inside any finite Galois
overfield `M/K`, the fixed subfields of `G^u H` realize the supporting lines of slope `u + 1` at
`embeddingOrbitCount K L M u`.

## Main definitions

* `TauCeti.slopePolygon K L`: lower convex envelope of subextension discriminant exponents.

## Main results

* `TauCeti.isConvexSeq_slopePolygon`, `TauCeti.le_slopePolygon`,
  `TauCeti.slopePolygon_ne_top_iff`, `TauCeti.slopePolygon_eq_top_iff`, `TauCeti.slopePolygon_one`,
  `TauCeti.slopePolygon_finrank`, `TauCeti.slopePolygon_le_discriminantExponent`,
  `TauCeti.slopePolygon_le_of_tower`, `TauCeti.slopePolygon_eq_of_algEquiv`.
* `TauCeti.slopePolygon_embeddingOrbitCount`, `TauCeti.isSupportingLine_slopePolygon_add_one`,
  `TauCeti.slopePolygon_eq_of_embeddingOrbitCount_eq`,
  `TauCeti.slopePolygon_of_index_lowerRamificationGroup_sup_le`.
* `TauCeti.slopePolygon_of_le_inertiaDegree`,
  `TauCeti.slopePolygon_of_inertiaDegree_le_of_le_mul_tameRamificationIndex`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 4, and Chapter IV, §3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  in *Représentations des groupes réductifs sur un corps local*, Hermann, 1984, Appendix, §A.6.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006),
  80–97 (arXiv:math/0309309), §3.
* The LMFDB Collaboration, *The L-functions and modular forms database*, local-field knowl
  `lf.slopes` (<https://www.lmfdb.org/knowledge/show/lf.slopes>).
-/

public section
noncomputable section

open IntermediateField MeasureTheory TauCeti.LocalFieldsRamification

namespace TauCeti

/-! ### Definition and basic properties of the slope polygon -/

section Basic

variable (K L : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]

/-- The **slope polygon** of a finite separable extension `L/K` of a nonarchimedean local field `K`:
the lower convex envelope of the minimal discriminant exponent among intermediate fields `E` of
`L/K` of each degree `n = [E : K]`, equipped with their canonical local-field structures. -/
def slopePolygon [Module.Finite K L] [Algebra.IsSeparable K L] : ℕ → WithTop ℝ :=
  lowerConvexEnvelope fun n =>
    ⨅ (E : IntermediateField K L) (_ : Module.finrank K E = n),
      haveI := Algebra.isSeparable_tower_bot_of_isSeparable K E L
      letI := finiteIntermediateFieldValuativeRel K L E
      letI := finiteIntermediateFieldTopology K L E
      letI := finiteIntermediateField_isNonarchimedeanLocalField K L E
      letI := finiteIntermediateField_valuativeExtension K L E
      (((discriminantExponent K E : ℕ) : ℝ) : WithTop ℝ)

/-- Defining formula for `slopePolygon` as a lower convex envelope over intermediate fields. -/
theorem slopePolygon_def [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L =
      lowerConvexEnvelope fun n =>
        ⨅ (E : IntermediateField K L) (_ : Module.finrank K E = n),
          haveI := Algebra.isSeparable_tower_bot_of_isSeparable K E L
          letI := finiteIntermediateFieldValuativeRel K L E
          letI := finiteIntermediateFieldTopology K L E
          letI := finiteIntermediateField_isNonarchimedeanLocalField K L E
          letI := finiteIntermediateField_valuativeExtension K L E
          (((discriminantExponent K E : ℕ) : ℝ) : WithTop ℝ) := (rfl)

private def intermediateFieldDiscriminant [Module.Finite K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) : ℕ :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  letI := finiteIntermediateFieldValuativeRel K L E
  letI := finiteIntermediateFieldTopology K L E
  letI := finiteIntermediateField_isNonarchimedeanLocalField K L E
  letI := finiteIntermediateField_valuativeExtension K L E
  discriminantExponent K E

private def subextensionPointHeight [Module.Finite K L] [Algebra.IsSeparable K L]
    (n : ℕ) : WithTop ℝ :=
  ⨅ (E : IntermediateField K L) (_ : Module.finrank K E = n),
    (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ)

private theorem slopePolygon_eq_lowerConvexEnvelope [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L = lowerConvexEnvelope (subextensionPointHeight K L) := rfl

private theorem withIntermediateFieldLocalField [Module.Finite K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) {P : Prop}
    (h : ∀ [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [ValuativeExtension K E] [Algebra.IsSeparable K E],
      intermediateFieldDiscriminant K L E = discriminantExponent K E → P) : P := by
  have := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let _ := finiteIntermediateFieldValuativeRel K L E
  let _ := finiteIntermediateFieldTopology K L E
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E
  have := finiteIntermediateField_valuativeExtension K L E
  exact h rfl

private theorem intermediateFieldDiscriminant_eq_of_algEquiv [Module.Finite K L]
    [Algebra.IsSeparable K L] (E : IntermediateField K L) {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F]
    [Algebra.IsSeparable K F] (e : E ≃ₐ[K] F) :
    intermediateFieldDiscriminant K L E = discriminantExponent K F :=
  withIntermediateFieldLocalField K L E fun h ↦
    h.trans (discriminantExponent_eq_of_algEquiv K E F e)

private theorem le_subextensionPointHeight [Module.Finite K L] [Algebra.IsSeparable K L]
    {n : ℕ} {x : WithTop ℝ}
    (hx : ∀ E : IntermediateField K L, Module.finrank K E = n →
      x ≤ (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ)) :
    x ≤ subextensionPointHeight K L n :=
  have : Nonempty (IntermediateField K L) := ⟨⊥⟩
  le_ciInf fun E ↦ by
    by_cases hE : Module.finrank K E = n
    · have : Nonempty (Module.finrank K E = n) := ⟨hE⟩; exact le_ciInf fun h ↦ hx E h
    · have : IsEmpty (Module.finrank K E = n) := ⟨hE⟩; simp

private theorem subextensionPointHeight_eq_top_of_forall_ne [Module.Finite K L]
    [Algebra.IsSeparable K L] {n : ℕ} (hn : ∀ E : IntermediateField K L, Module.finrank K E ≠ n) :
    subextensionPointHeight K L n = ⊤ :=
  eq_top_iff.2 <| le_subextensionPointHeight K L fun E hE ↦ absurd hE (hn E)

private theorem isSupportingLine_zero_subextensionPointHeight [Module.Finite K L]
    [Algebra.IsSeparable K L] : IsSupportingLine (subextensionPointHeight K L) 0 0 :=
  isSupportingLine_iff_forall.2 fun _ ↦ by
    simpa using le_subextensionPointHeight K L fun _ _ ↦ WithTop.coe_le_coe.2 (Nat.cast_nonneg _)

private theorem isAdmissible_subextensionPointHeight [Module.Finite K L] [Algebra.IsSeparable K L] :
    IsAdmissible (subextensionPointHeight K L) :=
  (isSupportingLine_zero_subextensionPointHeight K L).isAdmissible

private theorem subextensionPointHeight_zero [Module.Finite K L] [Algebra.IsSeparable K L] :
    subextensionPointHeight K L 0 = ⊤ :=
  subextensionPointHeight_eq_top_of_forall_ne K L fun _ ↦ Module.finrank_pos.ne'

private theorem subextensionPointHeight_eq_top_of_finrank_lt [Module.Finite K L]
    [Algebra.IsSeparable K L] {n : ℕ} (hn : Module.finrank K L < n) :
    subextensionPointHeight K L n = ⊤ :=
  subextensionPointHeight_eq_top_of_forall_ne K L fun E hE ↦ by
    have := Module.finrank_mul_finrank K E L
    have : 0 < Module.finrank E L := Module.finrank_pos; nlinarith

private theorem subextensionPointHeight_le [Module.Finite K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) :
    subextensionPointHeight K L (Module.finrank K E) ≤
      (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ) :=
  (ciInf_le ⟨0, Set.forall_mem_range.2 fun F ↦ by
    by_cases hF : Module.finrank K F = Module.finrank K E
    · have : Nonempty (Module.finrank K F = Module.finrank K E) := ⟨hF⟩
      exact le_ciInf fun _ ↦ WithTop.coe_le_coe.2 (Nat.cast_nonneg _)
    · have : IsEmpty (Module.finrank K F = Module.finrank K E) := ⟨hF⟩; simp⟩ E).trans
    (ciInf_le ⟨0, Set.forall_mem_range.2 fun _ ↦ WithTop.coe_le_coe.2 (Nat.cast_nonneg _)⟩ rfl)

private theorem subextensionPointHeight_one [Module.Finite K L] [Algebra.IsSeparable K L] :
    subextensionPointHeight K L 1 = 0 := by
  have hge := isSupportingLine_iff_forall.1 (isSupportingLine_zero_subextensionPointHeight K L) 1
  refine le_antisymm ?_ (by simpa using hge)
  have hdisc : intermediateFieldDiscriminant K L ⊥ = 0 := by
    rw [intermediateFieldDiscriminant_eq_of_algEquiv K L ⊥ (IntermediateField.botEquiv K L)]
    exact (discriminantExponent_eq_zero_iff K K).2 (isUnramified_of_finrank_eq_one (by simp))
  simpa [IntermediateField.finrank_bot, hdisc] using subextensionPointHeight_le K L ⊥

/-- The slope polygon of `L/K` is a convex height sequence. -/
theorem isConvexSeq_slopePolygon [Module.Finite K L] [Algebra.IsSeparable K L] :
    IsConvexSeq (slopePolygon K L) := isConvexSeq_lowerConvexEnvelope _

/-- **Universal property of `slopePolygon`.** Any convex height sequence `g` bounded above by
`δ(E/K)` at `[E : K]` for every intermediate field `E` of `L/K` (with its local-field structure
extending `K`) lies everywhere below `slopePolygon K L`. -/
theorem le_slopePolygon [Module.Finite K L] [Algebra.IsSeparable K L]
    {g : ℕ → WithTop ℝ} (hg : IsConvexSeq g)
    (hbound : ∀ (E : IntermediateField K L) [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [Algebra.IsSeparable K E],
      g (Module.finrank K E) ≤ (((discriminantExponent K E : ℕ) : ℝ) : WithTop ℝ)) :
    g ≤ slopePolygon K L :=
  le_lowerConvexEnvelope hg fun _ ↦ le_subextensionPointHeight K L fun E hE ↦
    withIntermediateFieldLocalField K L E fun h ↦ hE ▸ h ▸ hbound E

/-- Every height of `slopePolygon K L` is nonnegative. -/
theorem slopePolygon_nonneg [Module.Finite K L] [Algebra.IsSeparable K L] (n : ℕ) :
    (0 : WithTop ℝ) ≤ slopePolygon K L n := by
  simpa [slopePolygon_eq_lowerConvexEnvelope] using le_lowerConvexEnvelope (isConvexSeq_affine 0 0)
    (isSupportingLine_iff_forall.1 (isSupportingLine_zero_subextensionPointHeight K L)) n

/-- At index `0`, no subfield has degree `0`, so `slopePolygon K L 0 = ⊤`. -/
@[simp]
theorem slopePolygon_zero [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L 0 = ⊤ :=
  lowerConvexEnvelope_eq_top_of_forall_le fun _ hi ↦
    Nat.eq_zero_of_le_zero hi ▸ subextensionPointHeight_zero K L

/-- Beyond `[L : K]`, no subfield of `L/K` has degree `n`, so `slopePolygon K L n = ⊤`. -/
theorem slopePolygon_eq_top_of_finrank_lt [Module.Finite K L] [Algebra.IsSeparable K L]
    {n : ℕ} (hn : Module.finrank K L < n) : slopePolygon K L n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_forall_ge fun _ hk ↦
    subextensionPointHeight_eq_top_of_finrank_lt K L (hn.trans_le hk)

/-- At abscissa `1`, the base field `K` has discriminant exponent `0`, so `slopePolygon K L 1 = 0`.
-/
@[simp]
theorem slopePolygon_one [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L 1 = 0 := by
  rw [slopePolygon_eq_lowerConvexEnvelope, lowerConvexEnvelope_eq_of_forall_lt
      (isAdmissible_subextensionPointHeight K L) fun _ hn ↦
        Nat.lt_one_iff.1 hn ▸ subextensionPointHeight_zero K L, subextensionPointHeight_one]

/-- The finite domain of `slopePolygon K L` is the integer interval `[1, [L : K]]`. -/
theorem slopePolygon_ne_top_iff [Module.Finite K L] [Algebra.IsSeparable K L] {n : ℕ} :
    slopePolygon K L n ≠ ⊤ ↔ 1 ≤ n ∧ n ≤ Module.finrank K L := by
  refine ⟨fun hn ↦ ⟨Nat.pos_of_ne_zero fun h ↦ hn (h ▸ slopePolygon_zero K L),
    not_lt.1 fun h ↦ hn (slopePolygon_eq_top_of_finrank_lt K L h)⟩, fun ⟨h1, hle⟩ ↦ ?_⟩
  have hfin_le : slopePolygon K L (Module.finrank K L) ≤
      (((intermediateFieldDiscriminant K L ⊤ : ℕ) : ℝ) : WithTop ℝ) := by
    rw [slopePolygon_eq_lowerConvexEnvelope, ← IntermediateField.topEquiv.toLinearEquiv.finrank_eq
      (R := K) (M := (⊤ : IntermediateField K L))]
    exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
      (subextensionPointHeight_le K L ⊤)
  exact (isConvexSeq_slopePolygon K L).ne_top_of_le_of_le (by simp)
    (ne_top_of_le_ne_top WithTop.coe_ne_top hfin_le) h1 hle

/-- `slopePolygon K L n = ⊤` if and only if `n = 0` or `[L : K] < n`. -/
@[simp]
theorem slopePolygon_eq_top_iff [Module.Finite K L] [Algebra.IsSeparable K L] {n : ℕ} :
    slopePolygon K L n = ⊤ ↔ n = 0 ∨ Module.finrank K L < n := by
  rw [← not_iff_not, not_or, not_lt, ← ne_eq, ← ne_eq, ← Nat.one_le_iff_ne_zero]
  exact slopePolygon_ne_top_iff K L

/-- In a tower `L/E/K` where `E/K` is a compatible local-field extension, `slopePolygon K L` at
`[E : K]` is bounded above by `δ(E/K)`. -/
theorem slopePolygon_le_discriminantExponent (E : Type*)
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra K E] [ValuativeExtension K E] [Algebra E L] [IsScalarTower K E L]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    haveI := Algebra.isSeparable_tower_bot_of_isSeparable K E L
    slopePolygon K L (Module.finrank K E) ≤
      (((discriminantExponent K E : ℕ) : ℝ) : WithTop ℝ) := by
  have := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  have : Module.Finite K E := finite_of_valuativeExtension K E
  let e : E ≃ₐ[K] (IsScalarTower.toAlgHom K E L).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K E L)
  rw [slopePolygon_eq_lowerConvexEnvelope, ← e.symm.toLinearEquiv.finrank_eq,
    ← intermediateFieldDiscriminant_eq_of_algEquiv K L _ e.symm]
  exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
    (subextensionPointHeight_le K L _)

/-- In a tower `L/E/K` of finite separable extensions, `slopePolygon K L ≤ slopePolygon K E`. -/
theorem slopePolygon_le_of_tower (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L ≤ slopePolygon K E :=
  le_slopePolygon K E (isConvexSeq_slopePolygon K L) fun F _ _ _ _ _ ↦
    slopePolygon_le_discriminantExponent K L F

/-- At the top abscissa `[L : K]`, `slopePolygon K L [L : K] = δ(L/K)`. -/
@[simp]
theorem slopePolygon_finrank [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L (Module.finrank K L) =
      (((discriminantExponent K L : ℕ) : ℝ) : WithTop ℝ) := by
  have htop_disc := intermediateFieldDiscriminant_eq_of_algEquiv K L (⊤ : IntermediateField K L)
    IntermediateField.topEquiv
  have htop_deg : Module.finrank K (⊤ : IntermediateField K L) = Module.finrank K L :=
    IntermediateField.topEquiv.toLinearEquiv.finrank_eq
  rw [slopePolygon_eq_lowerConvexEnvelope, lowerConvexEnvelope_eq_of_forall_gt fun _ hn ↦
    subextensionPointHeight_eq_top_of_finrank_lt K L hn]
  refine le_antisymm (by rw [← htop_deg, ← htop_disc]; exact subextensionPointHeight_le K L ⊤)
    (le_subextensionPointHeight K L fun E hE ↦ by
      obtain rfl := IntermediateField.eq_of_le_of_finrank_eq le_top (hE.trans htop_deg.symm)
      simp [htop_disc])

private theorem subextensionPointHeight_le_of_algEquiv {L' : Type*} [Field L'] [Algebra K L']
    [Module.Finite K L] [Algebra.IsSeparable K L] [Module.Finite K L'] [Algebra.IsSeparable K L']
    (e : L ≃ₐ[K] L') (n : ℕ) :
    subextensionPointHeight K L n ≤ subextensionPointHeight K L' n :=
  le_subextensionPointHeight K L' fun E hE ↦
    withIntermediateFieldLocalField K L (E.map e.symm.toAlgHom) fun h ↦ by
      rw [intermediateFieldDiscriminant_eq_of_algEquiv K L' E (E.equivMap e.symm.toAlgHom), ← h,
        ← (E.equivMap e.symm.toAlgHom).symm.toLinearEquiv.finrank_eq.trans hE]
      exact subextensionPointHeight_le K L _

/-- `slopePolygon K L` is invariant under `K`-algebra equivalence of extensions. -/
theorem slopePolygon_eq_of_algEquiv {L' : Type*} [Field L'] [Algebra K L']
    [Module.Finite K L] [Algebra.IsSeparable K L] (e : L ≃ₐ[K] L') :
    slopePolygon K L =
      (haveI : Module.Finite K L' := Module.Finite.equiv e.toLinearEquiv
       haveI : Algebra.IsSeparable K L' := AlgEquiv.Algebra.isSeparable e
       slopePolygon K L') :=
  have : Module.Finite K L' := .equiv e.toLinearEquiv
  have : Algebra.IsSeparable K L' := AlgEquiv.Algebra.isSeparable e
  congrArg lowerConvexEnvelope <| funext fun n ↦
    le_antisymm (subextensionPointHeight_le_of_algEquiv K L e n)
      (subextensionPointHeight_le_of_algEquiv K L' e.symm n)

end Basic

/-! ### Vertex subextensions, supporting lines, and the slope-polygon theorem -/

section GaloisOverfield

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

private theorem le_intermediateFieldDiscriminant_of_upperIndex [Module.Finite K L]
    [Algebra.IsSeparable K L] (E : IntermediateField K L) (u : RamificationIndexDomain) :
    (∫ t in (-1 : ℝ)..u,
        ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩)) +
      ((u : ℝ) + 1) * ((Module.finrank K E : ℝ) - embeddingOrbitCount K L M u) ≤
      (intermediateFieldDiscriminant K L E : ℝ) :=
  withIntermediateFieldLocalField K L E fun hdisc ↦ by
    rw [hdisc]
    have hIoi := integrableOn_finrank_sub_embeddingOrbitCount_Ioi K E M
    have htail : 0 ≤ ∫ t in Set.Ioi (u : ℝ), ((Module.finrank K E : ℝ) -
        embeddingOrbitCount K E M ⟨max t (-1), le_max_right t (-1)⟩) :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ ↦
        sub_nonneg.2 (Nat.cast_le.2 (embeddingOrbitCount_le_finrank K E M _))
    have htrunc := intervalIntegral.integral_interval_add_Ioi hIoi
      (hIoi.mono_set (Set.Ioi_subset_Ioi u.property))
    rw [← discriminantExponent_eq_integral K E M] at htrunc
    have hfL := intervalIntegrable_const_sub_embeddingOrbitCount K L M
      (embeddingOrbitCount K L M u : ℝ) (-1) u
    have hmono := intervalIntegral.integral_mono u.property
      ((intervalIntegrable_const (c := (Module.finrank K E : ℝ) -
        embeddingOrbitCount K L M u)).add hfL)
      (intervalIntegrable_finrank_sub_embeddingOrbitCount K E M (-1) u) fun t ↦
        by linarith [Nat.cast_le (α := ℝ).2 (embeddingOrbitCount_le_of_tower K L M E
          ⟨max t (-1), le_max_right t (-1)⟩)]
    rw [intervalIntegral.integral_add intervalIntegrable_const hfL,
      intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at hmono
    linarith

private theorem isSupportingLine_subextensionPointHeight_add_one [Module.Finite K L]
    [Algebra.IsSeparable K L] (u : RamificationIndexDomain) :
    IsSupportingLine (subextensionPointHeight K L) ((u : ℝ) + 1)
      ((∫ t in (-1 : ℝ)..u, ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩)) -
        ((u : ℝ) + 1) * embeddingOrbitCount K L M u) :=
  isSupportingLine_iff_forall.2 fun _ ↦ le_subextensionPointHeight K L fun E hE ↦ by
    rw [WithTop.coe_le_coe, ← hE]
    linarith [le_intermediateFieldDiscriminant_of_upperIndex K L M E u]

private theorem exists_intermediateField_eq_orbitIntegral [Module.Finite K L]
    [Algebra.IsSeparable K L] (u : RamificationIndexDomain) :
    ∃ E : IntermediateField K L, Module.finrank K E = embeddingOrbitCount K L M u ∧
      (intermediateFieldDiscriminant K L E : ℝ) =
        ∫ t in (-1 : ℝ)..u, ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) := by
  let ι := IsScalarTower.toAlgHom K L M
  let H_u := upperRamificationGroup K M u ⊔ embeddingSubgroup K L M
  let E_u := ι.intermediateFieldEquivSubgroup.symm
    (OrderDual.toDual ⟨H_u, Set.mem_Ici.2 (embeddingSubgroup_def K L M ▸ le_sup_right)⟩)
  refine ⟨E_u, withIntermediateFieldLocalField K L E_u fun hdisc ↦ ?_⟩
  have heq : (OrderDual.ofDual (ι.intermediateFieldEquivSubgroup E_u)).val = H_u :=
    congrArg (fun x ↦ (OrderDual.ofDual x).val)
      (ι.intermediateFieldEquivSubgroup.apply_symm_apply _)
  have hemb : embeddingSubgroup K E_u M = H_u := by
    rw [embeddingSubgroup_def,
      (AlgHom.ext fun _ ↦ rfl : IsScalarTower.toAlgHom K E_u M = ι.comp E_u.val),
      IntermediateField.fieldRange_comp_val,
      ← AlgHom.coe_intermediateFieldEquivSubgroup_apply ι E_u, heq]
  have hdeg : Module.finrank K E_u = embeddingOrbitCount K L M u := by
    rw [← AlgHom.index_intermediateFieldEquivSubgroup_apply ι E_u, embeddingOrbitCount_def, heq]
  refine ⟨hdeg, ?_⟩
  rw [hdisc, discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le K E_u M
    (by rw [hemb]; exact le_sup_left)]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  have hle : (⟨max t (-1), le_max_right t (-1)⟩ : RamificationIndexDomain) ≤ u :=
    Subtype.mk_le_mk.2 (max_le (Set.uIoc_of_le u.property ▸ ht).2 u.property)
  rw [hdeg, embeddingOrbitCount_def K E_u M,
    embeddingOrbitCount_def K L M ⟨max t (-1), le_max_right t (-1)⟩, hemb, ← sup_assoc,
    sup_eq_left.2 (upperRamificationGroup_antitone K M hle)]

/-- **Explicit vertex heights of the slope polygon.** At every `u : RamificationIndexDomain`,
`slopePolygon K L (embeddingOrbitCount K L M u)` equals the truncated upper-index discriminant
integral `∫_{-1}^u ([G : G^u H] - [G : G^t H]) dt`. -/
theorem slopePolygon_embeddingOrbitCount [Module.Finite K L] [Algebra.IsSeparable K L]
    (u : RamificationIndexDomain) :
    slopePolygon K L (embeddingOrbitCount K L M u) =
      (((∫ t in (-1 : ℝ)..u, ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) : ℝ)) : WithTop ℝ) := by
  obtain ⟨E_u, hdeg, hdisc⟩ := exists_intermediateField_eq_orbitIntegral K L M u
  refine le_antisymm ?_ (le_trans (WithTop.coe_le_coe.2 (by ring_nf; exact le_rfl))
    (le_lowerConvexEnvelope (isConvexSeq_affine _ ((u : ℝ) + 1))
      (isSupportingLine_iff_forall.1 (isSupportingLine_subextensionPointHeight_add_one K L M u))
      (embeddingOrbitCount K L M u)))
  rw [slopePolygon_eq_lowerConvexEnvelope, ← hdisc, ← hdeg]
  exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
    (subextensionPointHeight_le K L E_u)

/-- For every `u : RamificationIndexDomain`, the affine line of slope `u + 1` passing through
`(embeddingOrbitCount K L M u, (slopePolygon K L (embeddingOrbitCount K L M u)).untop₀)` supports
`slopePolygon K L` from below. -/
theorem isSupportingLine_slopePolygon_add_one [Module.Finite K L] [Algebra.IsSeparable K L]
    (u : RamificationIndexDomain) :
    IsSupportingLine (slopePolygon K L) ((u : ℝ) + 1)
      ((slopePolygon K L (embeddingOrbitCount K L M u)).untop₀ -
        ((u : ℝ) + 1) * embeddingOrbitCount K L M u) := by
  rw [slopePolygon_embeddingOrbitCount K L M u, WithTop.untop₀_coe,
    slopePolygon_eq_lowerConvexEnvelope, (isLowerConvexEnvelope_lowerConvexEnvelope
      (isAdmissible_subextensionPointHeight K L)).isSupportingLine_iff]
  exact isSupportingLine_subextensionPointHeight_add_one K L M u

/-- Endpoint-integral calculation for `slopePolygon_eq_of_embeddingOrbitCount_eq`: when
`embeddingOrbitCount K L M` is constant on `(u, u']` (`u ≤ u'`), the vertex at `u'` lies on the
supporting line of slope `u + 1` through the vertex at `u`. -/
private theorem slopePolygon_embeddingOrbitCount_eq_of_forall_eq [Module.Finite K L]
    [Algebra.IsSeparable K L] {u u' : RamificationIndexDomain} (huu' : u ≤ u')
    (hconst : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v = embeddingOrbitCount K L M u') :
    slopePolygon K L (embeddingOrbitCount K L M u') =
      slopePolygon K L (embeddingOrbitCount K L M u) + ((((u : ℝ) + 1) *
        ((embeddingOrbitCount K L M u' : ℝ) - embeddingOrbitCount K L M u) : ℝ) : WithTop ℝ) := by
  rw [slopePolygon_embeddingOrbitCount K L M u', slopePolygon_embeddingOrbitCount K L M u,
    ← WithTop.coe_add, WithTop.coe_eq_coe, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_const_sub_embeddingOrbitCount K L M _ (-1) u)
      (intervalIntegrable_const_sub_embeddingOrbitCount K L M _ u u')]
  have hright : ∫ t in (u : ℝ)..u', ((embeddingOrbitCount K L M u' : ℝ) -
      embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (0 : ℝ))
      (Filter.Eventually.of_forall fun t ht ↦ by
        rw [Set.uIoc_of_le (Subtype.coe_le_coe.2 huu')] at ht
        have hmax : max t (-1) = t := max_eq_left (u.property.trans ht.1.le)
        rw [hconst ⟨max t (-1), le_max_right t (-1)⟩ (Subtype.mk_lt_mk.2 (hmax.symm ▸ ht.1))
          (Subtype.mk_le_mk.2 (hmax.symm ▸ ht.2)), sub_self]), intervalIntegral.integral_zero]
  have hsplit : (fun t : ℝ ↦ (embeddingOrbitCount K L M u' : ℝ) -
      embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) =
      fun t ↦ ((embeddingOrbitCount K L M u' : ℝ) - embeddingOrbitCount K L M u) +
        ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) := funext fun _ ↦ by ring
  rw [hright, add_zero, hsplit, intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_const_sub_embeddingOrbitCount K L M _ (-1) u),
    intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add, add_comm]

/-- **The slope-polygon theorem.** If `embeddingOrbitCount K L M v` is constant for `v ∈ (u, u']`,
then `slopePolygon K L` is affine of slope `u + 1` on `[embeddingOrbitCount K L M u,
embeddingOrbitCount K L M u']`. -/
theorem slopePolygon_eq_of_embeddingOrbitCount_eq [Module.Finite K L]
    [Algebra.IsSeparable K L] {u u' : RamificationIndexDomain}
    (hconst : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v = embeddingOrbitCount K L M u')
    (n : ℕ) (hn : embeddingOrbitCount K L M u ≤ n) (hn' : n ≤ embeddingOrbitCount K L M u') :
    slopePolygon K L n = slopePolygon K L (embeddingOrbitCount K L M u) +
      ((((u : ℝ) + 1) * ((n : ℝ) - embeddingOrbitCount K L M u) : ℝ) : WithTop ℝ) := by
  rcases le_or_gt u u' with huu' | hu'u
  · set n_u := embeddingOrbitCount K L M u
    have hy_u : slopePolygon K L n_u = (((slopePolygon K L n_u).untop₀ : ℝ) : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top (by
        rw [slopePolygon_embeddingOrbitCount K L M u]; exact WithTop.coe_ne_top)).symm
    have hmem_n := ((isConvexSeq_slopePolygon K L).ordConnected_supportingFace
      (isSupportingLine_slopePolygon_add_one K L M u)).out
      (mem_supportingFace.2 (by
        rw [hy_u, WithTop.untop₀_coe, WithTop.coe_eq_coe]; dsimp only [n_u]; ring))
      (mem_supportingFace.2 (by
        rw [slopePolygon_embeddingOrbitCount_eq_of_forall_eq K L M huu' hconst, hy_u,
          WithTop.untop₀_coe, ← WithTop.coe_add, WithTop.coe_eq_coe]; ring))
      ⟨hn, hn'⟩
    rw [mem_supportingFace.1 hmem_n, hy_u, WithTop.untop₀_coe, ← WithTop.coe_add,
      WithTop.coe_eq_coe]
    dsimp only [n_u]; ring
  · obtain rfl : n = embeddingOrbitCount K L M u :=
      le_antisymm (hn'.trans (embeddingOrbitCount_mono K L M hu'u.le)) hn
    simp

/-- On each Herbrand step `(φ_{M/K}(j), φ_{M/K}(j + 1)]` (`j : ℕ`), `slopePolygon K L` is affine
of slope `φ_{M/K}(j) + 1` between `[G : G_j H]` and `[G : G_{j + 1} H]`. For `j ≥ 1`, whenever
this step has a strict increase `[G : G_j H] < [G : G_{j + 1} H]`, `φ_{M/K}(j) + 1` is an Artin
slope appearing in `artinSlopeList K L M`. -/
theorem slopePolygon_of_index_lowerRamificationGroup_sup_le [Module.Finite K L]
    [Algebra.IsSeparable K L] (j : ℕ) {n : ℕ}
    (hn₁ : (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index ≤ n)
    (hn₂ : n ≤ (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔
      embeddingSubgroup K L M).index) :
    slopePolygon K L n =
      slopePolygon K L (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index +
        ((((herbrand K M ⟨j, Nat.cast_mem_ramificationIndexDomain j⟩ : ℝ) + 1) *
          ((n : ℝ) - (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index) : ℝ) :
            WithTop ℝ) := by
  have hocc (k : ℕ) : embeddingOrbitCount K L M
      (herbrand K M ⟨k, Nat.cast_mem_ramificationIndexDomain k⟩) =
      (lowerRamificationGroup K M k ⊔ embeddingSubgroup K L M).index := by
    rw [embeddingOrbitCount_herbrand]
    simpa using congrArg (fun G ↦ (G ⊔ embeddingSubgroup K L M).index)
      (lowerRamificationGroupReal_intCast K M k)
  rw [← hocc j] at hn₁ ⊢
  exact slopePolygon_eq_of_embeddingOrbitCount_eq K L M (fun v hv₁ hv₂ ↦ by
    rw [embeddingOrbitCount_def, upperRamificationGroup_eq_of_herbrand_lt_of_le K M hv₁ hv₂,
      hocc (j + 1)]) n hn₁ ((hocc (j + 1)).symm ▸ hn₂)

end GaloisOverfield

/-! ### Canonical unramified and tame segments of the slope polygon -/

section CanonicalSegments

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [Algebra.IsSeparable K L]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- Embeds `L/K` into its finite Galois normal closure inside `AlgebraicClosure K`, equipped with
its canonical local-field structure. -/
private theorem withGaloisOverfield {P : Prop}
    (h : ∀ (M : Type u) [Field M] [ValuativeRel M] [TopologicalSpace M]
      [IsNonarchimedeanLocalField M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
      [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M], P) : P := by
  have : Algebra.IsAlgebraic K L := .of_finite K L
  let Ω := AlgebraicClosure K
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  let _ : Algebra L Ω := ι.toRingHom.toAlgebra
  have : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  let M := IntermediateField.normalClosure K L Ω
  let _ := finiteIntermediateFieldValuativeRel K Ω M
  let _ := finiteIntermediateFieldTopology K Ω M
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω M
  have := finiteIntermediateField_valuativeExtension K Ω M
  exact h M

/-- **The unramified segment of the slope polygon.** On `[1, f(L/K)]`, `slopePolygon K L` vanishes
identically (slope `0`). -/
theorem slopePolygon_of_le_inertiaDegree {n : ℕ}
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ inertiaDegree K L) : slopePolygon K L n = 0 :=
  withGaloisOverfield K L fun M _ _ _ _ _ _ _ _ _ _ ↦ by
    simpa [slopePolygon_one] using slopePolygon_eq_of_embeddingOrbitCount_eq K L M
      (u := ⟨-1, le_rfl⟩) (u' := ⟨0, by norm_num⟩) (fun v hv₁ hv₂ ↦ by
        rw [embeddingOrbitCount_zero]
        exact embeddingOrbitCount_of_mem_Ioc_zero K L M
          (Subtype.coe_lt_coe.2 hv₁) (Subtype.coe_le_coe.2 hv₂))
      n (by simpa using hn₁) (by simpa using hn₂)

/-- **The tame segment of the slope polygon.** On `[f(L/K), f(L/K) · ε(L/K)]`, `slopePolygon K L`
has slope `1` and equals `n - f(L/K)`. -/
theorem slopePolygon_of_inertiaDegree_le_of_le_mul_tameRamificationIndex {n : ℕ}
    (hn₁ : inertiaDegree K L ≤ n) (hn₂ : n ≤ inertiaDegree K L * tameRamificationIndex K L) :
    slopePolygon K L n = (((n : ℝ) - inertiaDegree K L : ℝ) : WithTop ℝ) :=
  withGaloisOverfield K L fun M _ _ _ _ _ _ _ _ _ _ ↦ by
    have h0 : (herbrand K M ⟨((0 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain 0⟩ : ℝ) = 0 := by
      rw [herbrand_of_coe_le_zero K M (by norm_num)]; norm_num
    simpa [h0, slopePolygon_of_le_inertiaDegree K L (Nat.succ_le_of_lt inertiaDegree_pos) le_rfl]
      using slopePolygon_of_index_lowerRamificationGroup_sup_le K L M 0
        (by simpa using hn₁) (by simpa using hn₂)

end CanonicalSegments

end TauCeti
