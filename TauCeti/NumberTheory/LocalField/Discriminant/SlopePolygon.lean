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

/-!
# The slope polygon of a finite separable local-field extension

For a finite separable extension `L/K` of a nonarchimedean local field `K`, every intermediate field
`E` of `L/K` carries a canonical nonarchimedean local-field structure extending `K`, and hence a
local discriminant exponent `δ(E/K) = discriminantExponent K E`. Plotting at each degree `n : ℕ` the
infimum of `δ(E/K)` over intermediate fields `E` with `[E : K] = n` (or `⊤` when no such subfield
exists) and taking the lower convex envelope produces `TauCeti.slopePolygon K L : ℕ → WithTop ℝ`.

When `L` is embedded in a finite Galois local-field extension `M/K` with `G = Gal(M/K)` and
`H = Gal(M/L) = embeddingSubgroup K L M`, each upper ramification index `u ≥ -1` cuts out the fixed
subfield `E_u` of `G^u H` inside `L`, of degree
`[E_u : K] = [G : G^u H] = embeddingOrbitCount K L M u`.
Reading the upper-numbering integral `discriminantExponent_eq_integral` on an arbitrary subfield
`E` of `L/K`, dropping the nonnegative tail above `u`, and comparing orbit counts via `H ≤ Gal(M/E)`
shows that the affine line of slope `u + 1` through `([E_u : K], δ(E_u/K))` supports
`slopePolygon K L` from below and touches it at `[E_u : K]`. Whenever `[G : G^v H]` is constant for
`v ∈ (u, u']`, the right endpoint `[G : G^{u'} H]` lies on that same supporting line, so convexity
forces `slopePolygon K L` to be affine of slope `u + 1` across the entire interval
`[[G : G^u H], [G : G^{u'} H]]`.

Specializing to `(-1, 0]` and `(0, φ_{M/K}(1)]` recovers the slope-`0` unramified segment on
`[1, f(L/K)]` and the slope-`1` tame segment on `[f(L/K), f(L/K) · ε(L/K)]`, while the wild steps
`(φ_{M/K}(j), φ_{M/K}(j + 1)]` give segments of Artin slope `φ_{M/K}(j) + 1`.

## Main definitions

* `TauCeti.slopePolygon K L`: the lower convex envelope of subextension discriminant exponents of a
  finite separable extension `L/K`.

## Main results

* `TauCeti.isConvexSeq_slopePolygon`, `TauCeti.slopePolygon_ne_top_iff`: convexity and finite domain
  `[1, [L : K]]` of the slope polygon.
* `TauCeti.slopePolygon_one`, `TauCeti.slopePolygon_finrank`: endpoint values
  `slopePolygon K L 1 = 0` and `slopePolygon K L [L : K] = δ(L/K)`.
* `TauCeti.slopePolygon_le_discriminantExponent`: for any intermediate local field `E` in a tower
  `L/E/K`, `slopePolygon K L [E : K] ≤ δ(E/K)`.
* `TauCeti.slopePolygon_eq_of_algEquiv`: invariance of `slopePolygon K L` under `K`-algebra
  equivalence.
* `TauCeti.slopePolygon_embeddingOrbitCount`: explicit integral formula for `slopePolygon K L` at
  every orbit-count abscissa `embeddingOrbitCount K L M u`.
* `TauCeti.isSupportingLine_slopePolygon_add_one`: the line of slope `u + 1` through
  `embeddingOrbitCount K L M u` supports `slopePolygon K L`.
* `TauCeti.slopePolygon_eq_of_embeddingOrbitCount_eq`: **the slope-polygon theorem**; constancy of
  `embeddingOrbitCount K L M` on `(u, u']` makes `slopePolygon K L` affine of slope `u + 1` from
  `embeddingOrbitCount K L M u` to `embeddingOrbitCount K L M u'`.
* `TauCeti.slopePolygon_of_le_inertiaDegree` and
  `TauCeti.slopePolygon_of_inertiaDegree_le_of_le_mul_tameRamificationIndex`: the canonical
  unramified (slope `0`) and tame (slope `1`) segments.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 4.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  in *Représentations des groupes réductifs sur un corps local*, Hermann, 1984, Appendix, §A.6.
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
          (((discriminantExponent K E : ℕ) : ℝ) : WithTop ℝ) :=
  (rfl)

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
    slopePolygon K L = lowerConvexEnvelope (subextensionPointHeight K L) :=
  rfl

private theorem le_subextensionPointHeight [Module.Finite K L] [Algebra.IsSeparable K L]
    {n : ℕ} {x : WithTop ℝ}
    (hx : ∀ E : IntermediateField K L, Module.finrank K E = n →
      x ≤ (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ)) :
    x ≤ subextensionPointHeight K L n := by
  rw [subextensionPointHeight]
  have : Nonempty (IntermediateField K L) := ⟨⊥⟩
  refine le_ciInf fun E ↦ ?_
  by_cases hE : Module.finrank K E = n
  · have : Nonempty (Module.finrank K E = n) := ⟨hE⟩
    exact le_ciInf fun h ↦ hx E h
  · have : IsEmpty (Module.finrank K E = n) := ⟨hE⟩
    rw [WithTop.iInf_empty]
    exact le_top

private theorem subextensionPointHeight_eq_top_of_forall_ne [Module.Finite K L]
    [Algebra.IsSeparable K L] {n : ℕ}
    (hn : ∀ E : IntermediateField K L, Module.finrank K E ≠ n) :
    subextensionPointHeight K L n = ⊤ :=
  eq_top_iff.2 <| le_subextensionPointHeight K L fun E hE ↦ absurd hE (hn E)

private theorem isSupportingLine_zero_subextensionPointHeight [Module.Finite K L]
    [Algebra.IsSeparable K L] :
    IsSupportingLine (subextensionPointHeight K L) 0 0 := by
  rw [isSupportingLine_iff_forall]
  intro n
  simp only [zero_mul, add_zero]
  exact le_subextensionPointHeight K L fun _ _ ↦
    WithTop.coe_le_coe.2 (Nat.cast_nonneg _)

private theorem isAdmissible_subextensionPointHeight [Module.Finite K L]
    [Algebra.IsSeparable K L] :
    IsAdmissible (subextensionPointHeight K L) :=
  (isSupportingLine_zero_subextensionPointHeight K L).isAdmissible

private theorem subextensionPointHeight_zero [Module.Finite K L] [Algebra.IsSeparable K L] :
    subextensionPointHeight K L 0 = ⊤ :=
  subextensionPointHeight_eq_top_of_forall_ne K L fun _ ↦ Module.finrank_pos.ne'

private theorem subextensionPointHeight_eq_top_of_finrank_lt [Module.Finite K L]
    [Algebra.IsSeparable K L] {n : ℕ} (hn : Module.finrank K L < n) :
    subextensionPointHeight K L n = ⊤ := by
  refine subextensionPointHeight_eq_top_of_forall_ne K L fun E hE ↦ ?_
  have hmul := Module.finrank_mul_finrank K E L
  have hpos : 0 < Module.finrank E L := Module.finrank_pos
  have hle : Module.finrank K E ≤ Module.finrank K L := by
    nlinarith
  omega

private theorem subextensionPointHeight_le [Module.Finite K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) :
    subextensionPointHeight K L (Module.finrank K E) ≤
      (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ) := by
  rw [subextensionPointHeight]
  have hbdd_outer : BddBelow (Set.range fun F : IntermediateField K L ↦
      ⨅ (_ : Module.finrank K F = Module.finrank K E),
        (((intermediateFieldDiscriminant K L F : ℕ) : ℝ) : WithTop ℝ)) := by
    refine ⟨((0 : ℝ) : WithTop ℝ), ?_⟩
    rintro _ ⟨F, rfl⟩
    dsimp only
    by_cases hF : Module.finrank K F = Module.finrank K E
    · have : Nonempty (Module.finrank K F = Module.finrank K E) := ⟨hF⟩
      exact le_ciInf fun _ ↦ WithTop.coe_le_coe.2 (Nat.cast_nonneg _)
    · have : IsEmpty (Module.finrank K F = Module.finrank K E) := ⟨hF⟩
      rw [WithTop.iInf_empty]
      exact le_top
  refine (ciInf_le hbdd_outer E).trans ?_
  have hbdd_inner : BddBelow (Set.range fun _ : Module.finrank K E = Module.finrank K E ↦
      (((intermediateFieldDiscriminant K L E : ℕ) : ℝ) : WithTop ℝ)) :=
    ⟨((0 : ℝ) : WithTop ℝ), by
      rintro _ ⟨_, rfl⟩
      exact WithTop.coe_le_coe.2 (Nat.cast_nonneg _)⟩
  exact ciInf_le hbdd_inner rfl

private theorem intermediateFieldDiscriminant_eq_zero_of_finrank_eq_one [Module.Finite K L]
    [Algebra.IsSeparable K L] {E : IntermediateField K L} (hE : Module.finrank K E = 1) :
    intermediateFieldDiscriminant K L E = 0 := by
  dsimp only [intermediateFieldDiscriminant]
  have := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let _ := finiteIntermediateFieldValuativeRel K L E
  let _ := finiteIntermediateFieldTopology K L E
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E
  have := finiteIntermediateField_valuativeExtension K L E
  have : IsUnramified K E := isUnramified_of_finrank_eq_one (K := K) (L := E) hE
  exact (discriminantExponent_eq_zero_iff K E).2 this

private theorem subextensionPointHeight_one [Module.Finite K L] [Algebra.IsSeparable K L] :
    subextensionPointHeight K L 1 = 0 := by
  refine le_antisymm ?_ ?_
  · have hbot : Module.finrank K (⊥ : IntermediateField K L) = 1 := IntermediateField.finrank_bot
    have hle := hbot ▸ subextensionPointHeight_le K L (⊥ : IntermediateField K L)
    simpa [intermediateFieldDiscriminant_eq_zero_of_finrank_eq_one K L hbot] using hle
  · simpa using isSupportingLine_iff_forall.1
      (isSupportingLine_zero_subextensionPointHeight K L) 1

/-- The slope polygon of `L/K` is a convex height sequence. -/
theorem isConvexSeq_slopePolygon [Module.Finite K L] [Algebra.IsSeparable K L] :
    IsConvexSeq (slopePolygon K L) :=
  isConvexSeq_lowerConvexEnvelope _

/-- Every height of `slopePolygon K L` is nonnegative. -/
theorem slopePolygon_nonneg [Module.Finite K L] [Algebra.IsSeparable K L] (n : ℕ) :
    (0 : WithTop ℝ) ≤ slopePolygon K L n := by
  have hle := le_lowerConvexEnvelope (isConvexSeq_affine 0 0)
    (isSupportingLine_iff_forall.1 (isSupportingLine_zero_subextensionPointHeight K L)) n
  simpa [slopePolygon_eq_lowerConvexEnvelope] using hle

/-- At index `0`, no subfield has degree `0`, so `slopePolygon K L 0 = ⊤`. -/
@[simp]
theorem slopePolygon_zero [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L 0 = ⊤ := by
  rw [slopePolygon_eq_lowerConvexEnvelope]
  refine lowerConvexEnvelope_eq_top_of_forall_le fun i hi ↦ ?_
  obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
  exact subextensionPointHeight_zero K L

/-- Beyond `[L : K]`, no subfield of `L/K` has degree `n`, so `slopePolygon K L n = ⊤`. -/
theorem slopePolygon_eq_top_of_finrank_lt [Module.Finite K L] [Algebra.IsSeparable K L]
    {n : ℕ} (hn : Module.finrank K L < n) :
    slopePolygon K L n = ⊤ := by
  rw [slopePolygon_eq_lowerConvexEnvelope]
  exact lowerConvexEnvelope_eq_top_of_forall_ge fun k hk ↦
    subextensionPointHeight_eq_top_of_finrank_lt K L (hn.trans_le hk)

/-- At abscissa `1`, the base field `K` itself has discriminant exponent `0`, so
`slopePolygon K L 1 = 0`. -/
@[simp]
theorem slopePolygon_one [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L 1 = 0 := by
  rw [slopePolygon_eq_lowerConvexEnvelope,
    lowerConvexEnvelope_eq_of_forall_lt (isAdmissible_subextensionPointHeight K L) fun n hn ↦ by
      obtain rfl : n = 0 := by omega
      exact subextensionPointHeight_zero K L,
    subextensionPointHeight_one]

/-- The finite domain of `slopePolygon K L` is the integer interval `[1, [L : K]]`. -/
theorem slopePolygon_ne_top_iff [Module.Finite K L] [Algebra.IsSeparable K L] {n : ℕ} :
    slopePolygon K L n ≠ ⊤ ↔ 1 ≤ n ∧ n ≤ Module.finrank K L := by
  constructor
  · intro hn
    refine ⟨?_, ?_⟩
    · by_contra hlt
      obtain rfl : n = 0 := by omega
      exact hn (slopePolygon_zero K L)
    · by_contra hgt
      exact hn (slopePolygon_eq_top_of_finrank_lt K L (lt_of_not_ge hgt))
  · rintro ⟨h1, hle⟩
    have h1_ne : slopePolygon K L 1 ≠ ⊤ := by simp [slopePolygon_one]
    have htop_deg : Module.finrank K (⊤ : IntermediateField K L) = Module.finrank K L :=
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq
    have hfin_le : slopePolygon K L (Module.finrank K L) ≤
        (((intermediateFieldDiscriminant K L ⊤ : ℕ) : ℝ) : WithTop ℝ) := by
      rw [slopePolygon_eq_lowerConvexEnvelope, ← htop_deg]
      exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
        (subextensionPointHeight_le K L ⊤)
    have hfin_ne : slopePolygon K L (Module.finrank K L) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hfin_le
    exact (isConvexSeq_slopePolygon K L).ne_top_of_le_of_le h1_ne hfin_ne h1 hle

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
  let ι : E →ₐ[K] L := IsScalarTower.toAlgHom K E L
  let F : IntermediateField K L := ι.fieldRange
  let e : E ≃ₐ[K] F := AlgEquiv.ofInjectiveField ι
  have hdeg : Module.finrank K F = Module.finrank K E := e.symm.toLinearEquiv.finrank_eq
  have hdisc : intermediateFieldDiscriminant K L F = discriminantExponent K E := by
    dsimp only [intermediateFieldDiscriminant]
    have := Algebra.isSeparable_tower_bot_of_isSeparable K F L
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    exact (discriminantExponent_eq_of_algEquiv K E F e).symm
  rw [slopePolygon_eq_lowerConvexEnvelope, ← hdeg, ← hdisc]
  exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
    (subextensionPointHeight_le K L F)

/-- At the top abscissa `[L : K]`, the only intermediate field of degree `[L : K]` is `L` itself,
so `slopePolygon K L [L : K] = δ(L/K)`. -/
@[simp]
theorem slopePolygon_finrank [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [Module.Finite K L] [Algebra.IsSeparable K L] :
    slopePolygon K L (Module.finrank K L) =
      (((discriminantExponent K L : ℕ) : ℝ) : WithTop ℝ) := by
  rw [slopePolygon_eq_lowerConvexEnvelope,
    lowerConvexEnvelope_eq_of_forall_gt fun n hn ↦
      subextensionPointHeight_eq_top_of_finrank_lt K L hn]
  refine le_antisymm ?_ ?_
  · have htop_deg : Module.finrank K (⊤ : IntermediateField K L) = Module.finrank K L :=
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq
    have hle := htop_deg ▸ subextensionPointHeight_le K L (⊤ : IntermediateField K L)
    refine hle.trans_eq ?_
    congr 2
    dsimp only [intermediateFieldDiscriminant]
    have := Algebra.isSeparable_tower_bot_of_isSeparable K (⊤ : IntermediateField K L) L
    let _ := finiteIntermediateFieldValuativeRel K L (⊤ : IntermediateField K L)
    let _ := finiteIntermediateFieldTopology K L (⊤ : IntermediateField K L)
    have := finiteIntermediateField_isNonarchimedeanLocalField K L (⊤ : IntermediateField K L)
    have := finiteIntermediateField_valuativeExtension K L (⊤ : IntermediateField K L)
    exact discriminantExponent_eq_of_algEquiv K (⊤ : IntermediateField K L) L
      IntermediateField.topEquiv
  · refine le_subextensionPointHeight K L fun E hE ↦ ?_
    have htop : E = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top
      (hE.trans IntermediateField.topEquiv.toLinearEquiv.finrank_eq.symm)
    subst htop
    refine le_of_eq ?_
    congr 2
    dsimp only [intermediateFieldDiscriminant]
    have := Algebra.isSeparable_tower_bot_of_isSeparable K (⊤ : IntermediateField K L) L
    let _ := finiteIntermediateFieldValuativeRel K L (⊤ : IntermediateField K L)
    let _ := finiteIntermediateFieldTopology K L (⊤ : IntermediateField K L)
    have := finiteIntermediateField_isNonarchimedeanLocalField K L (⊤ : IntermediateField K L)
    have := finiteIntermediateField_valuativeExtension K L (⊤ : IntermediateField K L)
    exact (discriminantExponent_eq_of_algEquiv K (⊤ : IntermediateField K L) L
      IntermediateField.topEquiv).symm

/-- `slopePolygon K L` is invariant under `K`-algebra equivalence of extensions. -/
theorem slopePolygon_eq_of_algEquiv {L' : Type*} [Field L'] [Algebra K L']
    [Module.Finite K L] [Algebra.IsSeparable K L] (e : L ≃ₐ[K] L') :
    slopePolygon K L =
      (haveI : Module.Finite K L' := Module.Finite.equiv e.toLinearEquiv
       haveI : Algebra.IsSeparable K L' := AlgEquiv.Algebra.isSeparable e
       slopePolygon K L') := by
  have : Module.Finite K L' := Module.Finite.equiv e.toLinearEquiv
  have : Algebra.IsSeparable K L' := AlgEquiv.Algebra.isSeparable e
  have hpoint (E : IntermediateField K L) :
      intermediateFieldDiscriminant K L E =
        intermediateFieldDiscriminant K L' (E.map e.toAlgHom) := by
    dsimp only [intermediateFieldDiscriminant]
    have := Algebra.isSeparable_tower_bot_of_isSeparable K E L
    have := Algebra.isSeparable_tower_bot_of_isSeparable K (E.map e.toAlgHom) L'
    let _ := finiteIntermediateFieldValuativeRel K L E
    let _ := finiteIntermediateFieldTopology K L E
    have := finiteIntermediateField_isNonarchimedeanLocalField K L E
    have := finiteIntermediateField_valuativeExtension K L E
    let _ := finiteIntermediateFieldValuativeRel K L' (E.map e.toAlgHom)
    let _ := finiteIntermediateFieldTopology K L' (E.map e.toAlgHom)
    have := finiteIntermediateField_isNonarchimedeanLocalField K L' (E.map e.toAlgHom)
    have := finiteIntermediateField_valuativeExtension K L' (E.map e.toAlgHom)
    exact discriminantExponent_eq_of_algEquiv K E (E.map e.toAlgHom) (E.equivMap e.toAlgHom)
  have hsymm (E' : IntermediateField K L') :
      intermediateFieldDiscriminant K L' E' =
        intermediateFieldDiscriminant K L (E'.map e.symm.toAlgHom) := by
    dsimp only [intermediateFieldDiscriminant]
    have := Algebra.isSeparable_tower_bot_of_isSeparable K E' L'
    have := Algebra.isSeparable_tower_bot_of_isSeparable K (E'.map e.symm.toAlgHom) L
    let _ := finiteIntermediateFieldValuativeRel K L' E'
    let _ := finiteIntermediateFieldTopology K L' E'
    have := finiteIntermediateField_isNonarchimedeanLocalField K L' E'
    have := finiteIntermediateField_valuativeExtension K L' E'
    let _ := finiteIntermediateFieldValuativeRel K L (E'.map e.symm.toAlgHom)
    let _ := finiteIntermediateFieldTopology K L (E'.map e.symm.toAlgHom)
    have := finiteIntermediateField_isNonarchimedeanLocalField K L (E'.map e.symm.toAlgHom)
    have := finiteIntermediateField_valuativeExtension K L (E'.map e.symm.toAlgHom)
    exact discriminantExponent_eq_of_algEquiv K E' (E'.map e.symm.toAlgHom)
      (E'.equivMap e.symm.toAlgHom)
  rw [slopePolygon_eq_lowerConvexEnvelope, slopePolygon_eq_lowerConvexEnvelope]
  congr 1
  ext n
  refine le_antisymm ?_ ?_
  · refine le_subextensionPointHeight K L' fun E' hE' ↦ ?_
    have hdeg : Module.finrank K (E'.map e.symm.toAlgHom) = n :=
      (E'.equivMap e.symm.toAlgHom).symm.toLinearEquiv.finrank_eq.trans hE'
    rw [hsymm E', ← hdeg]
    exact subextensionPointHeight_le K L _
  · refine le_subextensionPointHeight K L fun E hE ↦ ?_
    have hdeg : Module.finrank K (E.map e.toAlgHom) = n :=
      (E.equivMap e.toAlgHom).symm.toLinearEquiv.finrank_eq.trans hE
    rw [hpoint E, ← hdeg]
    exact subextensionPointHeight_le K L' _

end Basic

/-! ### Vertex subextensions, supporting lines, and the slope-polygon theorem -/

section GaloisOverfield

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

private theorem intervalIntegrable_const_sub_embeddingOrbitCount (c : ℝ)
    (u : RamificationIndexDomain) :
    IntervalIntegrable
      (fun t : ℝ ↦ c - embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩)
      volume (-1 : ℝ) u := by
  have heq : (fun t : ℝ ↦ c - embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) =
      fun t : ℝ ↦ (c - Module.finrank K L) +
        ((Module.finrank K L : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) := by
    ext t
    ring
  rw [heq]
  exact intervalIntegrable_const.add
    (intervalIntegrable_finrank_sub_embeddingOrbitCount K L M le_rfl u.2)

/-- Lower bound on every subextension's discriminant exponent by the supporting line of slope
`u + 1` determined by the truncated orbit-count integral of `L/K`. -/
private theorem le_intermediateFieldDiscriminant_of_upperIndex [Module.Finite K L]
    [Algebra.IsSeparable K L] (E : IntermediateField K L) (u : RamificationIndexDomain) :
    (∫ t in (-1 : ℝ)..u,
        ((embeddingOrbitCount K L M u : ℝ) -
          embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩)) +
      ((u : ℝ) + 1) * ((Module.finrank K E : ℝ) - embeddingOrbitCount K L M u) ≤
      (intermediateFieldDiscriminant K L E : ℝ) := by
  dsimp only [intermediateFieldDiscriminant]
  have := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let _ := finiteIntermediateFieldValuativeRel K L E
  let _ := finiteIntermediateFieldTopology K L E
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E
  have := finiteIntermediateField_valuativeExtension K L E
  let fE : ℝ → ℝ := fun t ↦ (Module.finrank K E : ℝ) -
    embeddingOrbitCount K E M ⟨max t (-1), le_max_right t (-1)⟩
  let fL : ℝ → ℝ := fun t ↦ (embeddingOrbitCount K L M u : ℝ) -
    embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩
  have hIoi : IntegrableOn fE (Set.Ioi (-1 : ℝ)) :=
    integrableOn_finrank_sub_embeddingOrbitCount_Ioi K E M
  have htail_int : IntegrableOn fE (Set.Ioi (u : ℝ)) :=
    hIoi.mono_set (Set.Ioi_subset_Ioi u.2)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hIoi htail_int
  have htail_nonneg : 0 ≤ ∫ t in Set.Ioi (u : ℝ), fE t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ ↦
      sub_nonneg.2 (Nat.cast_le.2 (embeddingOrbitCount_le_finrank K E M _))
  have htrunc_le : ∫ t in (-1 : ℝ)..u, fE t ≤ (discriminantExponent K E : ℝ) := by
    rw [discriminantExponent_eq_integral K E M, ← hsplit]
    linarith
  have hfL_int : IntervalIntegrable fL volume (-1 : ℝ) u :=
    intervalIntegrable_const_sub_embeddingOrbitCount K L M _ u
  have hfE_int : IntervalIntegrable fE volume (-1 : ℝ) u :=
    intervalIntegrable_finrank_sub_embeddingOrbitCount K E M le_rfl u.2
  have hpointwise : (fun t : ℝ ↦ ((Module.finrank K E : ℝ) - embeddingOrbitCount K L M u) + fL t) ≤
      fE := by
    intro t
    have hle : embeddingOrbitCount K E M ⟨max t (-1), le_max_right t (-1)⟩ ≤
        embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩ := by
      rw [embeddingOrbitCount_def, embeddingOrbitCount_def]
      exact Subgroup.index_antitone (sup_le_sup_left (embeddingSubgroup_antitone K L M E) _)
    have hle' : (embeddingOrbitCount K E M ⟨max t (-1), le_max_right t (-1)⟩ : ℝ) ≤
        embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩ := Nat.cast_le.2 hle
    dsimp only [fL, fE]
    linarith
  have hmono := intervalIntegral.integral_mono u.2 (intervalIntegrable_const.add hfL_int)
    hfE_int hpointwise
  rw [intervalIntegral.integral_add intervalIntegrable_const hfL_int,
    intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at hmono
  exact le_trans (by dsimp only [fL] at hmono; linarith) htrunc_le

/-- Existence of the vertex subextension `E_u` of `L/K` fixed by `G^u H`, with degree
`embeddingOrbitCount K L M u` and discriminant exponent matching the truncated orbit-count
integral. -/
private theorem exists_intermediateField_eq_orbitIntegral [Module.Finite K L]
    [Algebra.IsSeparable K L] (u : RamificationIndexDomain) :
    ∃ E : IntermediateField K L,
      Module.finrank K E = embeddingOrbitCount K L M u ∧
        (intermediateFieldDiscriminant K L E : ℝ) =
          ∫ t in (-1 : ℝ)..u,
            ((embeddingOrbitCount K L M u : ℝ) -
              embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) := by
  let ι : L →ₐ[K] M := IsScalarTower.toAlgHom K L M
  let H_u : Subgroup (M ≃ₐ[K] M) := upperRamificationGroup K M u ⊔ embeddingSubgroup K L M
  let F_u : IntermediateField K M := IntermediateField.fixedField H_u
  have hF_le : F_u ≤ ι.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup ι.fieldRange, ← embeddingSubgroup_def K L M]
    exact IntermediateField.fixedField_le le_sup_right
  let E_u : IntermediateField K L := F_u.comap ι
  refine ⟨E_u, ?_⟩
  dsimp only [intermediateFieldDiscriminant]
  have := Algebra.isSeparable_tower_bot_of_isSeparable K E_u L
  let _ := finiteIntermediateFieldValuativeRel K L E_u
  let _ := finiteIntermediateFieldTopology K L E_u
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E_u
  have := finiteIntermediateField_valuativeExtension K L E_u
  have hfr : (IsScalarTower.toAlgHom K E_u M).fieldRange = F_u := by
    have hmap : E_u.map ι = F_u := IntermediateField.map_comap_eq_self hF_le
    ext y
    rw [← hmap, AlgHom.mem_fieldRange, IntermediateField.mem_map]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, hx⟩, fun ⟨z, hz, hy⟩ ↦ ⟨⟨z, hz⟩, hy⟩⟩
  have hemb : embeddingSubgroup K E_u M = H_u := by
    rw [embeddingSubgroup_def, hfr, IntermediateField.fixingSubgroup_fixedField]
  have hdeg : Module.finrank K E_u = embeddingOrbitCount K L M u := by
    rw [← index_embeddingSubgroup K E_u M, hemb, ← embeddingOrbitCount_def]
  refine ⟨hdeg, ?_⟩
  have hGu_le : upperRamificationGroup K M u ≤ embeddingSubgroup K E_u M := by
    rw [hemb]
    exact le_sup_left
  rw [discriminantExponent_eq_intervalIntegral_of_upperRamificationGroup_le K E_u M hGu_le]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [Set.uIoc_of_le u.2] at ht
  have hmax_le : (⟨max t (-1), le_max_right t (-1)⟩ : RamificationIndexDomain) ≤ u :=
    Subtype.mk_le_mk.2 (max_le ht.2 u.2)
  have hocc : embeddingOrbitCount K E_u M ⟨max t (-1), le_max_right t (-1)⟩ =
      embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩ := by
    have hant := upperRamificationGroup_antitone K M hmax_le
    rw [embeddingOrbitCount_def, embeddingOrbitCount_def, hemb, ← sup_assoc, sup_eq_left.2 hant]
  rw [hdeg, hocc]

/-- **Explicit vertex heights of the slope polygon.** At every upper ramification index `u ≥ -1`,
the height of `slopePolygon K L` at `embeddingOrbitCount K L M u` equals the truncated upper-index
discriminant integral `∫_{-1}^u ([G : G^u H] - [G : G^t H]) dt` (the discriminant exponent of the
subfield of `L` fixed by `G^u H`). -/
theorem slopePolygon_embeddingOrbitCount [Module.Finite K L] [Algebra.IsSeparable K L]
    (u : RamificationIndexDomain) :
    slopePolygon K L (embeddingOrbitCount K L M u) =
      (((∫ t in (-1 : ℝ)..u,
          ((embeddingOrbitCount K L M u : ℝ) -
            embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) : ℝ)) : WithTop ℝ) := by
  set I_u : ℝ := ∫ t in (-1 : ℝ)..u,
    ((embeddingOrbitCount K L M u : ℝ) -
      embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩)
  set c_u : ℝ := I_u - ((u : ℝ) + 1) * embeddingOrbitCount K L M u
  have hsupp : IsSupportingLine (subextensionPointHeight K L) ((u : ℝ) + 1) c_u := by
    rw [isSupportingLine_iff_forall]
    intro n
    refine le_subextensionPointHeight K L fun E hE ↦ ?_
    rw [WithTop.coe_le_coe, ← hE]
    have hle := le_intermediateFieldDiscriminant_of_upperIndex K L M E u
    dsimp only [c_u, I_u] at hle ⊢
    linarith
  obtain ⟨E_u, hdeg, hdisc⟩ := exists_intermediateField_eq_orbitIntegral K L M u
  change (intermediateFieldDiscriminant K L E_u : ℝ) = I_u at hdisc
  have hupper : slopePolygon K L (embeddingOrbitCount K L M u) ≤ ((I_u : ℝ) : WithTop ℝ) := by
    rw [slopePolygon_eq_lowerConvexEnvelope, ← hdeg, ← hdisc]
    exact (lowerConvexEnvelope_le (isAdmissible_subextensionPointHeight K L) _).trans
      (subextensionPointHeight_le K L E_u)
  have hlower : ((I_u : ℝ) : WithTop ℝ) ≤ slopePolygon K L (embeddingOrbitCount K L M u) := by
    have hmin := le_lowerConvexEnvelope (isConvexSeq_affine c_u ((u : ℝ) + 1))
      (isSupportingLine_iff_forall.1 hsupp) (embeddingOrbitCount K L M u)
    rw [← slopePolygon_eq_lowerConvexEnvelope] at hmin
    refine le_trans ?_ hmin
    rw [WithTop.coe_le_coe]
    dsimp only [c_u]
    linarith
  exact le_antisymm hupper hlower

/-- For every `u : RamificationIndexDomain`, the affine line of slope `u + 1` passing through
`(embeddingOrbitCount K L M u, (slopePolygon K L (embeddingOrbitCount K L M u)).untop₀)` supports
`slopePolygon K L` from below. -/
theorem isSupportingLine_slopePolygon_add_one [Module.Finite K L] [Algebra.IsSeparable K L]
    (u : RamificationIndexDomain) :
    IsSupportingLine (slopePolygon K L) ((u : ℝ) + 1)
      ((slopePolygon K L (embeddingOrbitCount K L M u)).untop₀ -
        ((u : ℝ) + 1) * embeddingOrbitCount K L M u) := by
  rw [slopePolygon_embeddingOrbitCount K L M u, WithTop.untop₀_coe,
    slopePolygon_eq_lowerConvexEnvelope,
    (isLowerConvexEnvelope_lowerConvexEnvelope
      (isAdmissible_subextensionPointHeight K L)).isSupportingLine_iff,
    isSupportingLine_iff_forall]
  intro n
  refine le_subextensionPointHeight K L fun E hE ↦ ?_
  rw [WithTop.coe_le_coe, ← hE]
  have hle := le_intermediateFieldDiscriminant_of_upperIndex K L M E u
  linarith

/-- **The slope-polygon theorem.** If `embeddingOrbitCount K L M v` is constant for `v ∈ (u, u']`,
then `slopePolygon K L` is affine of slope `u + 1` on the integer interval from
`embeddingOrbitCount K L M u` to `embeddingOrbitCount K L M u'`. -/
theorem slopePolygon_eq_of_embeddingOrbitCount_eq [Module.Finite K L]
    [Algebra.IsSeparable K L] {u u' : RamificationIndexDomain}
    (hconst : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v = embeddingOrbitCount K L M u')
    (n : ℕ) (hn : embeddingOrbitCount K L M u ≤ n) (hn' : n ≤ embeddingOrbitCount K L M u') :
    slopePolygon K L n =
      slopePolygon K L (embeddingOrbitCount K L M u) +
        ((((u : ℝ) + 1) * ((n : ℝ) - embeddingOrbitCount K L M u) : ℝ) : WithTop ℝ) := by
  rcases le_or_gt u u' with huu' | hu'u
  · set n_u := embeddingOrbitCount K L M u
    set n_u' := embeddingOrbitCount K L M u'
    set y_u := (slopePolygon K L n_u).untop₀
    set c_u := y_u - ((u : ℝ) + 1) * n_u
    have hy_u : slopePolygon K L n_u = (y_u : WithTop ℝ) := by
      refine (WithTop.coe_untop₀_of_ne_top ?_).symm
      rw [slopePolygon_embeddingOrbitCount K L M u]
      exact WithTop.coe_ne_top
    have hsupp : IsSupportingLine (slopePolygon K L) ((u : ℝ) + 1) c_u :=
      isSupportingLine_slopePolygon_add_one K L M u
    have hmem_u : n_u ∈ supportingFace (slopePolygon K L) ((u : ℝ) + 1) c_u := by
      rw [mem_supportingFace, hy_u, WithTop.coe_eq_coe]
      dsimp only [c_u]
      ring
    have hmem_u' : n_u' ∈ supportingFace (slopePolygon K L) ((u : ℝ) + 1) c_u := by
      rw [mem_supportingFace, slopePolygon_embeddingOrbitCount K L M u', WithTop.coe_eq_coe]
      have hy_u_int : y_u = ∫ t in (-1 : ℝ)..u,
          ((n_u : ℝ) - embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩) := by
        dsimp only [y_u]
        rw [slopePolygon_embeddingOrbitCount K L M u, WithTop.untop₀_coe]
      let g : ℝ → ℝ := fun t ↦
        (n_u' : ℝ) - embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩
      have hg_left : IntervalIntegrable g volume (-1 : ℝ) u :=
        intervalIntegrable_const_sub_embeddingOrbitCount K L M _ u
      have hg_right : IntervalIntegrable g volume (u : ℝ) u' := by
        have hg_full : IntervalIntegrable g volume (-1 : ℝ) u' :=
          intervalIntegrable_const_sub_embeddingOrbitCount K L M _ u'
        rw [intervalIntegrable_iff] at hg_full ⊢
        refine hg_full.mono_set ?_
        rw [Set.uIoc_of_le (Subtype.mk_le_mk.1 huu'), Set.uIoc_of_le u'.2]
        exact Set.Ioc_subset_Ioc u.2 le_rfl
      have hsplit := (intervalIntegral.integral_add_adjacent_intervals hg_left hg_right).symm
      have hright_zero : ∫ t in (u : ℝ)..u', g t = 0 := by
        have hcongr : ∫ t in (u : ℝ)..u', g t = ∫ _ in (u : ℝ)..u', (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
          rw [Set.uIoc_of_le (Subtype.mk_le_mk.1 huu')] at ht
          have ht_ge : -1 ≤ t := u.2.trans ht.1.le
          have hv_gt : u < ⟨max t (-1), le_max_right t (-1)⟩ :=
            Subtype.mk_lt_mk.2 (by rw [max_eq_left ht_ge]; exact ht.1)
          have hv_le : (⟨max t (-1), le_max_right t (-1)⟩ : RamificationIndexDomain) ≤ u' :=
            Subtype.mk_le_mk.2 (by rw [max_eq_left ht_ge]; exact ht.2)
          dsimp only [g, n_u']
          rw [hconst _ hv_gt hv_le, sub_self]
        rw [hcongr, intervalIntegral.integral_zero]
      have hleft_shift : ∫ t in (-1 : ℝ)..u, g t =
          ((u : ℝ) + 1) * ((n_u' : ℝ) - n_u) + y_u := by
        let fL : ℝ → ℝ := fun t ↦
          (n_u : ℝ) - embeddingOrbitCount K L M ⟨max t (-1), le_max_right t (-1)⟩
        have hfL_int : IntervalIntegrable fL volume (-1 : ℝ) u :=
          intervalIntegrable_const_sub_embeddingOrbitCount K L M _ u
        have hfun : g = fun t ↦ ((n_u' : ℝ) - n_u) + fL t := by
          ext t
          dsimp only [g, fL]
          ring
        rw [hfun, intervalIntegral.integral_add intervalIntegrable_const hfL_int,
          intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add, hy_u_int]
      change ∫ t in (-1 : ℝ)..u', g t = c_u + ((u : ℝ) + 1) * n_u'
      rw [hsplit, hright_zero, add_zero, hleft_shift]
      dsimp only [c_u]
      ring
    have hmem_n : n ∈ supportingFace (slopePolygon K L) ((u : ℝ) + 1) c_u :=
      ((isConvexSeq_slopePolygon K L).ordConnected_supportingFace hsupp).out hmem_u hmem_u'
        ⟨hn, hn'⟩
    rw [mem_supportingFace.1 hmem_n, hy_u, ← WithTop.coe_add, WithTop.coe_eq_coe]
    dsimp only [c_u]
    ring
  · have hmono : embeddingOrbitCount K L M u' ≤ embeddingOrbitCount K L M u :=
      embeddingOrbitCount_mono K L M hu'u.le
    obtain rfl : n = embeddingOrbitCount K L M u := le_antisymm (hn'.trans hmono) hn
    simp

/-- On each Herbrand step `(φ_{M/K}(j), φ_{M/K}(j + 1)]` (`j : ℕ`), `slopePolygon K L` is affine
of slope `φ_{M/K}(j) + 1` between `[G : G_j H]` and `[G : G_{j + 1} H]`. For `j ≥ 1`, these are the
Artin slopes appearing in `artinSlopeList K L M`. -/
theorem slopePolygon_of_index_lowerRamificationGroup_sup_le [Module.Finite K L]
    [Algebra.IsSeparable K L] (j : ℕ) {n : ℕ}
    (hn₁ : (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index ≤ n)
    (hn₂ : n ≤ (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).index) :
    slopePolygon K L n =
      slopePolygon K L (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index +
        ((((herbrand K M ⟨j, Nat.cast_mem_ramificationIndexDomain j⟩ : ℝ) + 1) *
          ((n : ℝ) - (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index) : ℝ) :
            WithTop ℝ) := by
  let u : RamificationIndexDomain := herbrand K M ⟨j, Nat.cast_mem_ramificationIndexDomain j⟩
  let u' : RamificationIndexDomain :=
    herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩
  have hu_occ : embeddingOrbitCount K L M u =
      (lowerRamificationGroup K M j ⊔ embeddingSubgroup K L M).index := by
    rw [embeddingOrbitCount_def, upperRamificationGroup_def, inverseHerbrand_herbrand]
    have h1 := lowerRamificationGroupReal_intCast K M j
    simp only [Int.cast_natCast] at h1
    rw [h1]
  have hconst_step : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v =
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).index := by
    intro v hvu hvu'
    have hψ₁ : (j : ℝ) < (inverseHerbrand K M v : ℝ) := by
      have hlt := inverseHerbrand_strictMono K M hvu
      rwa [inverseHerbrand_herbrand] at hlt
    have hψ₂ : (inverseHerbrand K M v : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hle := (inverseHerbrand_strictMono K M).monotone hvu'
      rwa [inverseHerbrand_herbrand] at hle
    have hG : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def]
      apply lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((j + 1 : ℕ) : ℤ))
      · push_cast
        linarith
      · exact_mod_cast hψ₂
    rw [embeddingOrbitCount_def, hG]
  have hu_lt_u' : u < u' :=
    herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by exact_mod_cast Nat.lt_succ_self j))
  have hu'_occ : embeddingOrbitCount K L M u' =
      (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).index :=
    hconst_step u' hu_lt_u' le_rfl
  rw [← hu_occ] at hn₁ ⊢
  rw [← hu'_occ] at hn₂
  exact slopePolygon_eq_of_embeddingOrbitCount_eq K L M
    (fun v hvu hvu' ↦ (hconst_step v hvu hvu').trans hu'_occ.symm) n hn₁ hn₂

end GaloisOverfield

/-! ### Canonical unramified and tame segments of the slope polygon -/

section CanonicalSegments

variable (K L : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [Algebra.IsSeparable K L]

/-- **The unramified segment of the slope polygon.** On `[1, f(L/K)]`, `slopePolygon K L` vanishes
identically (slope `0`). -/
theorem slopePolygon_of_le_inertiaDegree {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ inertiaDegree K L) :
    slopePolygon K L n = 0 := by
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let Ω := AlgebraicClosure K
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  let _ : Algebra L Ω := ι.toRingHom.toAlgebra
  have : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let _ := finiteIntermediateFieldValuativeRel K Ω M
  let _ := finiteIntermediateFieldTopology K Ω M
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω M
  have := finiteIntermediateField_valuativeExtension K Ω M
  let u : RamificationIndexDomain := ⟨-1, le_rfl⟩
  let u' : RamificationIndexDomain := ⟨0, by norm_num⟩
  have hu : embeddingOrbitCount K L M u = 1 := embeddingOrbitCount_neg_one K L M
  have hu' : embeddingOrbitCount K L M u' = inertiaDegree K L := embeddingOrbitCount_zero K L M
  have hconst : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v = embeddingOrbitCount K L M u' := fun v hv₁ hv₂ ↦ by
    rw [hu']
    exact embeddingOrbitCount_of_mem_Ioc_zero K L M
      (Subtype.mk_lt_mk.1 hv₁) (Subtype.mk_le_mk.1 hv₂)
  have hpoly := slopePolygon_eq_of_embeddingOrbitCount_eq K L M hconst n
    (hu.symm ▸ hn₁) (hu'.symm ▸ hn₂)
  simpa [u, hu, slopePolygon_one] using hpoly

/-- **The tame segment of the slope polygon.** On `[f(L/K), f(L/K) · ε(L/K)]`, `slopePolygon K L`
has slope `1` and equals `n - f(L/K)`. -/
theorem slopePolygon_of_inertiaDegree_le_of_le_mul_tameRamificationIndex {n : ℕ}
    (hn₁ : inertiaDegree K L ≤ n)
    (hn₂ : n ≤ inertiaDegree K L * tameRamificationIndex K L) :
    slopePolygon K L n = (((n : ℝ) - inertiaDegree K L : ℝ) : WithTop ℝ) := by
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let Ω := AlgebraicClosure K
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  let _ : Algebra L Ω := ι.toRingHom.toAlgebra
  have : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let _ := finiteIntermediateFieldValuativeRel K Ω M
  let _ := finiteIntermediateFieldTopology K Ω M
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω M
  have := finiteIntermediateField_valuativeExtension K Ω M
  let u : RamificationIndexDomain := ⟨0, by norm_num⟩
  let u' : RamificationIndexDomain := herbrand K M ⟨1, by norm_num⟩
  have hu_eq : u = herbrand K M ⟨0, by norm_num⟩ :=
    (herbrand_of_coe_le_zero K M le_rfl).symm
  have hu_occ : embeddingOrbitCount K L M u = inertiaDegree K L := embeddingOrbitCount_zero K L M
  have hconst_step : ∀ v : RamificationIndexDomain, u < v → v ≤ u' →
      embeddingOrbitCount K L M v = inertiaDegree K L * tameRamificationIndex K L := by
    intro v hvu hvu'
    have hψ₁ : (0 : ℝ) < (inverseHerbrand K M v : ℝ) := by
      rw [hu_eq] at hvu
      have hlt := inverseHerbrand_strictMono K M hvu
      rwa [inverseHerbrand_herbrand] at hlt
    have hψ₂ : (inverseHerbrand K M v : ℝ) ≤ 1 := by
      have hle := (inverseHerbrand_strictMono K M).monotone hvu'
      rwa [inverseHerbrand_herbrand] at hle
    have hG : upperRamificationGroup K M v = lowerRamificationGroup K M 1 := by
      rw [upperRamificationGroup_def]
      exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := 1)
        (by simpa using hψ₁) (by simpa using hψ₂)
    rw [embeddingOrbitCount_def, hG, index_lowerRamificationGroup_one_sup_embeddingSubgroup]
  have hu_lt_u' : u < u' := by
    rw [hu_eq]
    exact herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by norm_num))
  have hu'_occ : embeddingOrbitCount K L M u' = inertiaDegree K L * tameRamificationIndex K L :=
    hconst_step u' hu_lt_u' le_rfl
  have hpoly := slopePolygon_eq_of_embeddingOrbitCount_eq K L M
    (fun v hvu hvu' ↦ (hconst_step v hvu hvu').trans hu'_occ.symm) n
    (hu_occ.symm ▸ hn₁) (hu'_occ.symm ▸ hn₂)
  have hf_zero : slopePolygon K L (inertiaDegree K L) = 0 :=
    slopePolygon_of_le_inertiaDegree K L (Nat.succ_le_of_lt inertiaDegree_pos) le_rfl
  simpa [u, hu_occ, hf_zero] using hpoly

end CanonicalSegments

end TauCeti
