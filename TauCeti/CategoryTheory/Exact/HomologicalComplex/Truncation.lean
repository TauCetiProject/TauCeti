/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Bounded truncations of maps with acyclic mapping cone

Let `E` be an exact structure and `r : Y ⟶ I` a map of complexes whose mapping cone `C` is
acyclic, with `Y` vanishing in degrees `> n`. Above `n` the cone is `I` itself, so `I` is acyclic
there, and it can be cut off at the cycles `Zⁿ⁺¹(C) ↣ Iⁿ⁺¹`:

```text
T = (⋯ → Iⁿ⁻¹ → Iⁿ ↠ Zⁿ⁺¹(C) → 0),      j : T ⟶ I,
```

with `j` the identity in degrees `≤ n` and the inflation in degree `n + 1`. The map `r` factors as
`Y ⟶ T ⟶ I`, and the mapping cone of `Y ⟶ T` is acyclic: it is the truncation of `C` at its
cycles `Zⁿ⁺¹(C)`, `TauCeti.ExactStructure.AcyclicData.acyclic_of_truncation`. When `Y` is bounded
and `I` is bounded below, `T` is bounded, so this replaces a bounded below resolution of a bounded
complex by a bounded one, compatibly with the original.

The truncation is constructed for `n = -1` and moved to any `n` by shifting.

## Main results

* `TauCeti.ExactStructure.exists_truncation_of_acyclic_mappingCone`: the truncation, with its
  properties.

## References

* Bernhard Keller, *Derived categories and their uses*, Handbook of Algebra 1 (1996),
  Lemma 11.7, for the comparison of bounded and bounded below derived categories of an exact
  category, which these truncations serve.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CochainComplex.mappingCone ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace TruncationAtZero

variable {Y I : CochainComplex C ℤ} {r : Y ⟶ I}
  (hC : E.AcyclicData (CochainComplex.mappingCone r))

/-- The terms of the truncation: those of `I` in negative degrees, the cycles `Z⁰` of the cone in
degree `0`, and zero above. -/
private noncomputable def X : ℤ → C
  | Int.negSucc k => I.X (Int.negSucc k)
  | Int.ofNat 0 => hC.Z 0
  | Int.ofNat (_ + 1) => 0

/-- The differentials of the truncation: those of `I` below `-1`, and `I⁻¹ ⟶ C⁻¹ ↠ Z⁰`. -/
private noncomputable def d : ∀ m, X hC m ⟶ X hC (m + 1)
  | Int.negSucc 0 => (inr r).f (Int.negSucc 0) ≫ hC.p (Int.negSucc 0)
  | Int.negSucc (k + 1) => I.d (Int.negSucc (k + 1)) (Int.negSucc k)
  | Int.ofNat _ => 0

private theorem d_comp_d (m : ℤ) : d hC m ≫ d hC (m + 1) = 0 :=
  match m with
  | Int.negSucc 0 => comp_zero
  | Int.negSucc 1 => by
    -- `d` is defined by matching on the degree, and `Int.negSucc 1 + 1` reduces to
    -- `Int.negSucc 0` only by evaluation, so `change` states the two differentials.
    change I.d (Int.negSucc 1) (Int.negSucc 0) ≫ (inr r).f (Int.negSucc 0) ≫
      hC.p (Int.negSucc 0) = 0
    have h : hC.p (Int.negSucc 1) ≫ hC.i (Int.negSucc 0) =
        (CochainComplex.mappingCone r).d (Int.negSucc 1) (Int.negSucc 0) := hC.fac _
    have hz : hC.i (Int.negSucc 0) ≫ hC.p (Int.negSucc 0) = 0 := hC.zero _
    rw [← (inr r).comm_assoc, ← h, Category.assoc, hz, comp_zero, comp_zero]
  | Int.negSucc (k + 2) => I.d_comp_d _ _ _
  | Int.ofNat _ => zero_comp

/-- The truncation `(⋯ → I⁻² → I⁻¹ ↠ Z⁰ → 0)`. -/
private noncomputable def complex : CochainComplex C ℤ :=
  CochainComplex.of (X hC) (d hC) (d_comp_d hC)


variable [Y.IsStrictlyLE (-1)]

omit [HasZeroObject C] in
/-- The second projection of the cone in degree `0` is split by the inclusion, since `Y¹ = 0`. -/
private theorem snd_inr (φ : Y ⟶ I) :
    (snd φ).v 0 0 (add_zero 0) ≫ (inr φ).f 0 = 𝟙 _ := by
  rw [← id_X φ 0 1 rfl,
    (Y.isZero_of_isStrictlyLE (-1) 1 (by lia)).eq_of_tgt ((fst φ).1.v 0 1 rfl) 0, zero_comp,
    zero_add]

/-- The components of the inclusion `T ⟶ I`. -/
private noncomputable def jf : ∀ m, X hC m ⟶ I.X m
  | Int.negSucc _ => 𝟙 _
  | Int.ofNat 0 => hC.i 0 ≫ (snd r).v 0 0 (add_zero 0)
  | Int.ofNat (_ + 1) => 0

private theorem mono_jf_zero : Mono (jf hC 0) := by
  have := (E.isInflation_f (hC.conflation 0)).mono
  have : Mono ((snd r).v 0 0 (add_zero 0)) :=
    ⟨fun g₁ g₂ h ↦ by simpa [snd_inr r] using h =≫ (inr r).f 0⟩
  exact mono_comp (hC.i 0) ((snd r).v 0 0 (add_zero 0))

omit [Y.IsStrictlyLE (-1)] in
/-- The differential of the truncation followed by the inclusion in degree `0`. -/
private theorem d_jf_neg_one :
    (inr r).f (Int.negSucc 0) ≫ hC.p (Int.negSucc 0) ≫ jf hC 0 = I.d (Int.negSucc 0) 0 := by
  have h : hC.p (Int.negSucc 0) ≫ hC.i 0 =
      (CochainComplex.mappingCone r).d (Int.negSucc 0) 0 := hC.fac _
  -- Unfold `jf hC 0`, defined by matching on the degree.
  change (inr r).f (Int.negSucc 0) ≫ hC.p (Int.negSucc 0) ≫ hC.i 0 ≫ (snd r).v 0 0 (add_zero 0) =
    _
  rw [reassoc_of% h, (inr r).comm_assoc, inr_f_snd_v, Category.comp_id]

private theorem jf_comm (m : ℤ) :
    d hC m ≫ jf hC (m + 1) = jf hC m ≫ I.d m (m + 1) :=
  match m with
  | Int.negSucc 0 =>
    (Category.assoc _ _ _).trans ((d_jf_neg_one hC).trans (Category.id_comp _).symm)
  | Int.negSucc (k + 1) => by
    -- In negative degrees `d` is the differential of `I` and `jf` is the identity, by the matches
    -- defining them; `Int.negSucc (k + 1) + 1` reduces to `Int.negSucc k` only by evaluation.
    change I.d (Int.negSucc (k + 1)) (Int.negSucc k) ≫ 𝟙 _ =
      𝟙 _ ≫ I.d (Int.negSucc (k + 1)) (Int.negSucc k)
    simp
  | Int.ofNat 0 => by
    -- `d hC 0 = 0` and `jf hC 0 = i ≫ snd`, by the matches defining them.
    change 0 ≫ jf hC 1 = (hC.i 0 ≫ (snd r).v 0 0 (add_zero 0)) ≫ I.d 0 1
    have h := d_snd_v r 0 1 rfl
    rw [(Y.isZero_of_isStrictlyLE (-1) 1 (by lia)).eq_of_src (r.f 1) 0, comp_zero, zero_add] at h
    have hf : hC.p 0 ≫ hC.i 1 = (CochainComplex.mappingCone r).d 0 1 := hC.fac 0
    have hz : hC.i 0 ≫ (CochainComplex.mappingCone r).d 0 1 = 0 := by
      rw [← hf, ← Category.assoc, hC.zero, zero_comp]
    rw [zero_comp, Category.assoc, ← h, reassoc_of% hz, zero_comp]
  | Int.ofNat (k + 1) => (isZero_zero C).eq_of_src _ _

/-- The inclusion `T ⟶ I`: the identity in negative degrees and `Z⁰ ↣ C⁰ = I⁰` in degree `0`. -/
private noncomputable def j : complex hC ⟶ I where
  f := jf hC
  comm' := by
    rintro m _ rfl
    dsimp only [complex]
    rw [CochainComplex.of_d]
    exact (jf_comm hC m).symm

/-- The components of the factorization `Y ⟶ T`. -/
private noncomputable def rf : ∀ m, Y.X m ⟶ X hC m
  | Int.negSucc _ => r.f _
  | Int.ofNat _ => 0

private theorem rf_comm (m : ℤ) : Y.d m (m + 1) ≫ rf hC (m + 1) = rf hC m ≫ d hC m :=
  match m with
  | Int.negSucc 0 => by
    have := mono_jf_zero hC
    -- In degree `0` the factorization is zero. In degree `-1`, its composite with the
    -- monomorphism `jf hC 0` is `r ≫ I.d = Y.d ≫ r`, which vanishes since `Y⁰ = 0`.
    have h : r.f (Int.negSucc 0) ≫ (inr r).f (Int.negSucc 0) ≫ hC.p (Int.negSucc 0) ≫ jf hC 0 =
        0 := by
      rw [d_jf_neg_one, r.comm, (Y.isZero_of_isStrictlyLE (-1) 0 (by lia)).eq_of_tgt
        (Y.d (Int.negSucc 0) 0) 0, zero_comp]
    -- The codomain `Z (-1 + 1)` of `hC.p (-1)` is the source `X 0` of `jf hC 0` only after
    -- evaluating `-1 + 1`, so `rw [Category.assoc]` does not apply and the reassociation is a term.
    have key : (r.f (Int.negSucc 0) ≫ (inr r).f (Int.negSucc 0) ≫ hC.p (Int.negSucc 0)) ≫
        jf hC 0 = 0 ≫ jf hC 0 :=
      (Category.assoc _ _ _).trans ((congrArg (r.f (Int.negSucc 0) ≫ ·)
        (Category.assoc _ _ _)).trans (h.trans zero_comp.symm))
    exact comp_zero.trans ((cancel_mono (jf hC 0)).1 key).symm
  | Int.negSucc (k + 1) => (r.comm (Int.negSucc (k + 1)) (Int.negSucc k)).symm
  | Int.ofNat _ => (Y.isZero_of_isStrictlyLE (-1) _ (by lia)).eq_of_src _ _

/-- The factorization `Y ⟶ T` of `r`. -/
private noncomputable def r' : Y ⟶ complex hC where
  f := rf hC
  comm' := by
    rintro m _ rfl
    dsimp only [complex]
    rw [CochainComplex.of_d]
    exact (rf_comm hC m).symm

private theorem r'_j : r' hC ≫ j hC = r := by
  ext m
  match m with
  | Int.negSucc _ => exact Category.comp_id _
  | Int.ofNat k => exact (Y.isZero_of_isStrictlyLE (-1) _ (by lia)).eq_of_src _ _

private theorem r'_j_comm : r' hC ≫ j hC = 𝟙 Y ≫ r := by
  rw [r'_j, Category.id_comp]

/-- The map of mapping cones `Cone(Y ⟶ T) ⟶ Cone(Y ⟶ I)` induced by the inclusion. -/
private noncomputable abbrev coneMap :
    CochainComplex.mappingCone (r' hC) ⟶ CochainComplex.mappingCone r :=
  map (r' hC) r (𝟙 Y) (j hC) (r'_j_comm hC)

private instance : (CochainComplex.mappingCone (r' hC)).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k + 1 := ⟨(i - 1).toNat, by lia⟩
  rw [isZero_X_iff]
  exact ⟨Y.isZero_of_isStrictlyLE (-1) _ (by lia), isZero_zero C⟩

private theorem isIso_coneMap_f (m : ℤ) (hm : m < 0) : IsIso ((coneMap hC).f m) := by
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hm
  have : IsIso ((𝟙 Y : Y ⟶ Y).f (Int.negSucc k + 1)) := by
    rw [HomologicalComplex.id_f]
    infer_instance
  -- In negative degrees `j` is the identity, by the match defining its components.
  have : IsIso ((j hC).f (Int.negSucc k)) := inferInstanceAs (IsIso (𝟙 _))
  exact isIso_map_f _ _ _ _ _ _ _ rfl

/-- The degree-`0` term of `Cone(Y ⟶ T)` is `T⁰ = Z⁰`, since `Y¹ = 0`. -/
private noncomputable def coneIso : (CochainComplex.mappingCone (r' hC)).X 0 ≅ hC.Z 0 where
  hom := (snd (r' hC)).v 0 0 (add_zero 0)
  inv := (inr (r' hC)).f 0
  hom_inv_id := snd_inr (r' hC)
  inv_hom_id := inr_f_snd_v _ 0

private theorem coneIso_hom_i : (coneIso hC).hom ≫ hC.i 0 = (coneMap hC).f 0 := by
  apply ext_to r 0 1 rfl
  · exact (Y.isZero_of_isStrictlyLE (-1) 1 (by lia)).eq_of_tgt _ _
  · rw [map_f_snd_v, Category.assoc]
    -- `(j hC).f 0` is `hC.i 0 ≫ snd`, by the match defining the components of `j`.
    rfl

private theorem acyclic_mappingCone_r' : E.acyclic (CochainComplex.mappingCone (r' hC)) :=
  hC.acyclic_of_truncation (coneMap hC) (isIso_coneMap_f hC) (coneIso hC) (coneIso_hom_i hC)

end TruncationAtZero

open TruncationAtZero in
/-- The truncation for `n = -1`. -/
private theorem exists_truncation_zero {Y I : CochainComplex C ℤ} (r : Y ⟶ I)
    (hr : E.acyclic (CochainComplex.mappingCone r)) [Y.IsStrictlyLE (-1)] :
    ∃ (T : CochainComplex C ℤ) (j : T ⟶ I) (r' : Y ⟶ T), r' ≫ j = r ∧
      (∀ k ≤ -1, IsIso (j.f k)) ∧ Mono (j.f 0) ∧ T.IsStrictlyLE 0 ∧
      (∀ a, I.IsStrictlyGE a → T.IsStrictlyGE (min a 0)) ∧
      E.acyclic (CochainComplex.mappingCone r') := by
  obtain ⟨hC⟩ := (E.acyclic_iff _).1 hr
  refine ⟨complex hC, j hC, r' hC, r'_j hC, fun k hk ↦ ?_, mono_jf_zero hC, ?_, fun a ha ↦ ?_,
    acyclic_mappingCone_r' hC⟩
  · obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero (show k < 0 by lia)
    -- In negative degrees `j` is the identity, by the match defining its components.
    exact inferInstanceAs (IsIso (𝟙 _))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k + 1 := ⟨(i - 1).toNat, by lia⟩
    exact isZero_zero C
  · rw [CochainComplex.isStrictlyLE_iff, CochainComplex.isStrictlyGE_iff] at *
    intro i hi
    obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero (show i < 0 by lia)
    exact ha _ (by lia)


/-- **Bounded truncations of maps with acyclic mapping cone.** Let `r : Y ⟶ I` have acyclic
mapping cone, with `Y` vanishing in degrees `> n`. Then `r` factors as `r' ≫ j` with these
properties:
* `j : T ⟶ I` is an isomorphism in degrees `≤ n` and a monomorphism in degree `n + 1`;
* `T` vanishes in degrees `> n + 1`, and is bounded below whenever `I` is;
* the mapping cone of `r' : Y ⟶ T` is acyclic.

Here `T` is `I` cut off at the cycles `Zⁿ⁺¹ ↣ Iⁿ⁺¹` of the mapping cone of `r`. -/
theorem exists_truncation_of_acyclic_mappingCone {Y I : CochainComplex C ℤ} (r : Y ⟶ I)
    (hr : E.acyclic (CochainComplex.mappingCone r)) (n : ℤ) [Y.IsStrictlyLE n] :
    ∃ (T : CochainComplex C ℤ) (j : T ⟶ I) (r' : Y ⟶ T), r' ≫ j = r ∧
      (∀ k ≤ n, IsIso (j.f k)) ∧ Mono (j.f (n + 1)) ∧ T.IsStrictlyLE (n + 1) ∧
      (∀ a, I.IsStrictlyGE a → T.IsStrictlyGE (min a (n + 1))) ∧
      E.acyclic (CochainComplex.mappingCone r') := by
  have : (Y⟦n + 1⟧).IsStrictlyLE (-1) := Y.isStrictlyLE_shift n (n + 1) (-1) (by lia)
  obtain ⟨hC⟩ := (E.acyclic_iff _).1 hr
  obtain ⟨T, j, r', hr'j, hiso, hmono, _, hge, hT⟩ := exists_truncation_zero (r⟦n + 1⟧')
    (E.acyclic.prop_of_iso (CochainComplex.mappingCone.shiftIso r (n + 1))
      (hC.shift (n + 1)).acyclic)
  obtain ⟨hT⟩ := (E.acyclic_iff _).1 hT
  let eI := (shiftFunctorCompIsoId (CochainComplex C ℤ) (n + 1) (-(n + 1)) (by lia)).app I
  let eY := (shiftFunctorCompIsoId (CochainComplex C ℤ) (n + 1) (-(n + 1)) (by lia)).app Y
  have hcomp : eY.inv ≫ r'⟦-(n + 1)⟧' ≫ j⟦-(n + 1)⟧' ≫ eI.hom = r := by
    rw [← Functor.map_comp_assoc, hr'j]
    simp only [eI, eY, Iso.app_hom, Iso.app_inv]
    rw [← Functor.comp_map, NatTrans.naturality, Iso.inv_hom_id_app_assoc, Functor.id_map]
  have hmono₀ (k : ℤ) (hk : k = 0) : Mono (j.f k) := by
    subst hk
    exact hmono
  refine ⟨T⟦-(n + 1)⟧, j⟦-(n + 1)⟧' ≫ eI.hom, eY.inv ≫ r'⟦-(n + 1)⟧', by
    simpa only [Category.assoc] using hcomp, fun k hk ↦ ?_, ?_,
    T.isStrictlyLE_shift 0 (-(n + 1)) (n + 1) (by lia), fun a ha ↦ ?_, ?_⟩
  · have := hiso (k + -(n + 1)) (by lia)
    rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
    infer_instance
  · have := hmono₀ (n + 1 + -(n + 1)) (by lia)
    rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
    infer_instance
  · have : (I⟦n + 1⟧).IsStrictlyGE (a - (n + 1)) := I.isStrictlyGE_shift a (n + 1) _ (by lia)
    have := hge _ this
    exact T.isStrictlyGE_shift (min (a - (n + 1)) 0) (-(n + 1)) _ (by lia)
  · exact E.acyclic_mappingCone_of_iso eY.symm (Iso.refl _) (by simp)
      (E.acyclic.prop_of_iso (CochainComplex.mappingCone.shiftIso r' (-(n + 1)))
        (hT.shift (-(n + 1))).acyclic)

end TauCeti.ExactStructure
