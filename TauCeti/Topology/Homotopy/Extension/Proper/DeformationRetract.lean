/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Proper.Basic

/-!
# Proper cofibrations and proper strong deformation retractions

Let `A ⊆ X` have the proper homotopy extension property. When the inclusion `A → X` is proper and
admits a proper homotopy inverse `g : X → A` — with jointly proper homotopies `g ∘ incl ≃ id_A` on
`I × A` and `incl ∘ g ≃ id_X` on `I × X` — `A` is a *proper strong deformation retract* of `X`:
there exist a proper retraction `r : X → A` fixing `A` pointwise and a proper homotopy relative to
`A` from `id_X` to `incl ∘ r` (`TauCeti.properStrongDeformationRetract_of_inverse`).

Following Hatcher (Proposition 0.19) while retaining joint properness on cylinders at each step:
1. Extending `g ∘ incl ≃ id_A` from `A` to `X` replaces `g` by a proper retraction `r : X → A`
   properly homotopic to `g`
   (`TauCeti.HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic`).
2. Concatenating `id_X ≃ incl ∘ r` with its reverse postcomposed with `incl ∘ r` retraces itself on
   `A`, and extending the tent cutoff from `{0, 1} × X ∪ I × A` to `I × X` makes the homotopy
   stationary on `A` while preserving properness
   (`TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`).

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic`: rectifying a
  proper homotopy left inverse of the inclusion to a proper retraction.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`,
  `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retraction`: rectifying
  retracing proper homotopies and proper retractions relative to `A`.
* `TauCeti.properStrongDeformationRetract_of_inverse`,
  `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff`:
  **proper strong deformation retraction characterization** for proper cofibrations.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Section 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0,
  Proposition 0.19.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap Set Topology unitInterval

universe u

section Retracing

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f₀ f₁ f₂ : C(X, Y)}

/-- Cutoff tent time `(u, t) ↦ projIcc 0 1 (min (2 t) (2 - 2 t) - u)` contracting the tent
reparametrization on `I` to `0` as `u` goes from `0` to `1`. -/
private def retracingTime (u t : I) : I :=
  projIcc 0 1 zero_le_one (min (2 * (t : ℝ)) (2 - 2 * t) - u)

private lemma continuous_retracingTime :
    Continuous fun p : I × I ↦ retracingTime p.1 p.2 := by
  unfold retracingTime; fun_prop

private lemma retracingTime_zero_right (u : I) : retracingTime u 0 = 0 :=
  projIcc_of_le_left zero_le_one <| by
    rw [Icc.coe_zero]; linarith [min_le_left (2 * (0 : ℝ)) (2 - 2 * 0), u.2.1]

private lemma retracingTime_one_right (u : I) : retracingTime u 1 = 0 :=
  projIcc_of_le_left zero_le_one <| by
    rw [Icc.coe_one]; linarith [min_le_right (2 * (1 : ℝ)) (2 - 2 * 1), u.2.1]

private lemma retracingTime_one_left (t : I) : retracingTime 1 t = 0 :=
  projIcc_of_le_left zero_le_one <| by
    rw [Icc.coe_one]
    rcases le_total (t : ℝ) (1 / 2) with ht | ht
    · linarith [min_le_left (2 * (t : ℝ)) (2 - 2 * t)]
    · linarith [min_le_right (2 * (t : ℝ)) (2 - 2 * t)]

/-- At `u = 0` and any point where `G` retraces `F`, `F (retracingTime 0 t, x)` agrees with the
concatenation `(F.trans G) (t, x)`. -/
private lemma apply_retracingTime_zero (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) {x : X}
    (hretr : ∀ t, G (t, x) = F (σ t, x)) (t : I) :
    F (retracingTime 0 t, x) = (F.trans G) (t, x) := by
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · dsimp only at ht
    congr 2
    rw [retracingTime, Icc.coe_zero, sub_zero, min_eq_left (by linarith)]
    exact projIcc_of_mem zero_le_one ⟨by linarith [t.2.1], by linarith⟩
  · dsimp only at ht
    rw [hretr, retracingTime, Icc.coe_zero, sub_zero, min_eq_right (by linarith)]
    congr 2; ext
    rw [coe_projIcc, coe_symm_eq, min_eq_right (by linarith), max_eq_right (by linarith [t.2.2])]
    ring

/-- The cylinder boundary `{0, 1} × X ∪ I × A` inside `I × X`. -/
private abbrev cylinderBoundary (A : Set X) : Set (I × X) :=
  ({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A

/-- Proper partial homotopy on `I × ({0, 1} × X ∪ I × A)` keeping `{0} × X` at `f₀`, `{1} × X` at
`f₂`, and contracting the tent paths `(t, a) ↦ F (retracingTime 0 t, a)` on `I × A` to `f₀`. -/
private theorem exists_proper_retracing_boundary_homotopy (hA_closed : IsClosed A)
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hF : IsProperMap F) (hG : IsProperMap G)
    (hretr : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    ∃ Φ : C(I × cylinderBoundary A, Y), IsProperMap Φ ∧
      (∀ b : cylinderBoundary A, Φ (0, b) = (F.trans G) b.1) ∧
      (∀ x : X, Φ (1, ⟨(0, x), Or.inl ⟨Or.inl rfl, trivial⟩⟩) = f₀ x) ∧
      (∀ x : X, Φ (1, ⟨(1, x), Or.inl ⟨Or.inr rfl, trivial⟩⟩) = f₂ x) ∧
      ∀ (t : I) {x : X} (hx : x ∈ A), Φ (1, ⟨(t, x), Or.inr ⟨trivial, hx⟩⟩) = f₀ x := by
  classical
  let B := cylinderBoundary A
  have hB : IsClosed B :=
    ((Set.toFinite _).isClosed.prod isClosed_univ).union (isClosed_univ.prod hA_closed)
  have hπX : IsProperMap (fun q : I × B ↦ q.2.1.2) :=
    (isProperMap_snd_of_compactSpace (X := I)).comp
      (hB.isProperMap_subtypeVal.comp (isProperMap_snd_of_compactSpace (X := I)))
  let raw : I × B → Y := fun q ↦
    if q.2.1.2 ∈ A then F (retracingTime q.1 q.2.1.1, q.2.1.2)
    else if q.2.1.1 = 0 then f₀ q.2.1.2 else f₂ q.2.1.2
  let sSide : Set (I × B) := {q | q.2.1.2 ∈ A}
  let sLeft : Set (I × B) := {q | q.2.1.1 = 0}
  let sRight : Set (I × B) := {q | q.2.1.1 = 1}
  have hsSide : IsClosed sSide := hA_closed.preimage (by fun_prop)
  have hsLeft : IsClosed sLeft := isClosed_eq (by fun_prop) continuous_const
  have hsRight : IsClosed sRight := isClosed_eq (by fun_prop) continuous_const
  have hcov : sSide ∪ (sLeft ∪ sRight) = univ :=
    Set.eq_univ_of_forall fun q ↦ q.2.2.elim (fun h ↦ .inr h.1) fun h ↦ .inl h.2
  have hraw : IsProperMap raw := by
    refine IsProperMap.of_union_isClosed hsSide (hsLeft.union hsRight) hcov ?_ ?_
    · convert hF.comp ((hπX.comp hsSide.isProperMap_subtypeVal).prodMk_of_t2_left
        (continuous_retracingTime.comp
          (by fun_prop : Continuous fun z : sSide ↦ (z.1.1, z.1.2.1.1)))) using 1
      ext z
      exact ite_eq_left z.2
    · have hsL' : IsClosed (Subtype.val ⁻¹' sLeft : Set ↑(sLeft ∪ sRight)) :=
        hsLeft.preimage continuous_subtype_val
      have hsR' : IsClosed (Subtype.val ⁻¹' sRight : Set ↑(sLeft ∪ sRight)) :=
        hsRight.preimage continuous_subtype_val
      have hπLR : IsProperMap (fun z : ↑(sLeft ∪ sRight) ↦ z.1.2.1.2) :=
        hπX.comp (hsLeft.union hsRight).isProperMap_subtypeVal
      refine IsProperMap.of_union_isClosed hsL' hsR' (Set.eq_univ_of_forall Subtype.prop) ?_ ?_
      · convert (F.isProperMap_left hF).comp (hπLR.comp hsL'.isProperMap_subtypeVal) using 1
        funext z
        have hz : z.1.1.2.1.1 = 0 := z.2
        by_cases hx : z.1.1.2.1.2 ∈ A <;> simp [raw, hx, hz, retracingTime_zero_right]
      · convert (G.isProperMap_right hG).comp (hπLR.comp hsR'.isProperMap_subtypeVal) using 1
        funext z
        have hz : z.1.1.2.1.1 = 1 := z.2
        by_cases hx : z.1.1.2.1.2 ∈ A
        · have hf₂₀ : f₂ z.1.1.2.1.2 = f₀ z.1.1.2.1.2 := by
            rw [← G.apply_one, hretr 1 _ hx, symm_one, F.apply_zero]
          simp [raw, hx, hz, retracingTime_one_right, hf₂₀]
        · simp [raw, hx, hz]
  refine ⟨⟨raw, hraw.continuous⟩, hraw, fun ⟨⟨t, x⟩, hb⟩ ↦ ?_, fun x ↦ ?_, fun x ↦ ?_,
    fun t x hx ↦ by simp [raw, hx, retracingTime_one_left]⟩
  · by_cases hx : x ∈ A
    · simpa [raw, hx] using apply_retracingTime_zero F G (fun s ↦ hretr s x hx) t
    · rcases hb with ⟨ht | ht, -⟩ | ⟨-, hxA⟩
      · simp [raw, hx, show t = 0 from ht]
      · simp [raw, hx, show t = 1 from ht]
      · exact (hx hxA).elim
  · by_cases hx : x ∈ A <;> simp [raw, hx, retracingTime_zero_right]
  · by_cases hx : x ∈ A
    · have hf₂₀ : f₀ x = f₂ x := by rw [← G.apply_one, hretr 1 x hx, symm_one, F.apply_zero]
      simpa [raw, hx, retracingTime_one_right] using hf₂₀
    · simp [raw, hx]

/-- **A proper homotopy which retraces itself on a closed proper cofibration can be made stationary
on `A`.** Let `F : f₀.Homotopy f₁` and `G : f₁.Homotopy f₂` be proper homotopies such that, at every
point of a closed subset `A` with the proper homotopy extension property, `G` runs backwards along
`F`. Then there is a proper homotopy from `f₀` to `f₂` relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing
    (hA : HasProperHomotopyExtensionProperty A) (hA_closed : IsClosed A)
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hF : IsProperMap F) (hG : IsProperMap G)
    (hretr : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    ∃ H : f₀.HomotopyRel f₂ A, IsProperMap H := by
  obtain ⟨Φ, hΦ, hΦ₀, hΦ_left, hΦ_right, hΦ_side⟩ :=
    exists_proper_retracing_boundary_homotopy hA_closed F G hF hG hretr
  obtain ⟨Ψ, hΨ, -, hΨ₁⟩ :=
    (hA.zero_one_prod_univ_union_univ_prod hA_closed).exists_extension
      (F.trans G).toContinuousMap (Homotopy.isProperMap_trans hF hG) Φ hΦ hΦ₀
  refine ⟨{ toContinuousMap := Ψ.comp ⟨fun p ↦ (1, p), by fun_prop⟩
            map_zero_left := fun x ↦ (hΨ₁ 1 ⟨(0, x), .inl ⟨.inl rfl, trivial⟩⟩).trans (hΦ_left x)
            map_one_left := fun x ↦ (hΨ₁ 1 ⟨(1, x), .inl ⟨.inr rfl, trivial⟩⟩).trans (hΦ_right x)
            prop' := fun t _ hx ↦ (hΨ₁ 1 ⟨(t, _), .inr ⟨trivial, hx⟩⟩).trans (hΦ_side t hx) },
    hΨ.comp (isProperMap_prodMk_left (1 : I))⟩

end Retracing

section DeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A proper homotopy left inverse `g : X → A` of the inclusion of a subset with the proper homotopy
extension property is properly homotopic to a proper retraction `r : X → A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic
    (hA : HasProperHomotopyExtensionProperty A) (g : C(X, A)) (hg : IsProperMap g)
    (H : (g.comp (subtypeVal A)).Homotopy (ContinuousMap.id A)) (hH : IsProperMap H) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r a = a) ∧ ∃ K : r.Homotopy g, IsProperMap K := by
  obtain ⟨G, hG, hG₀, hG₁⟩ := hA.exists_extension g hg H.toContinuousMap hH fun a ↦ H.apply_zero a
  refine ⟨G.comp ⟨fun x ↦ (1, x), by fun_prop⟩, hG.comp (isProperMap_prodMk_left (1 : I)),
    fun a ↦ (hG₁ 1 a).trans (H.apply_one a),
    Homotopy.symm { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ ↦ rfl },
    Homotopy.isProperMap_symm hG⟩

/-- A retraction `r : X → A` onto a closed subset `A` with the proper homotopy extension property
whose composite with the inclusion is properly homotopic to `id_X` is properly homotopic to `id_X`
relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retraction
    (hA : HasProperHomotopyExtensionProperty A) (hA_closed : IsClosed A) {r : C(X, A)}
    (hr : ∀ a : A, r a = a)
    (K : ((subtypeVal A).comp r).Homotopy (ContinuousMap.id X)) (hK : IsProperMap K) :
    ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H := by
  let ir : C(X, X) := (subtypeVal A).comp r
  let F : (ContinuousMap.id X).Homotopy ir := K.symm
  have hF : IsProperMap F := Homotopy.isProperMap_symm hK
  have hir_idem : ir.comp ir = ir := ContinuousMap.ext fun x ↦ congrArg Subtype.val (hr (r x))
  let G : ir.Homotopy ir := (F.symm.compContinuousMap ir).cast hir_idem (ContinuousMap.id_comp ir)
  refine hA.exists_proper_homotopyRel_of_retracing hA_closed F G hF
    ((Homotopy.isProperMap_cast_iff _ _).2
      (Homotopy.isProperMap_compContinuousMap (Homotopy.isProperMap_symm hF)
        (Homotopy.isProperMap_left hK))) fun t x hx ↦ ?_
  have hrx : ir x = x := congrArg Subtype.val (hr ⟨x, hx⟩)
  simp [G, F, hrx]

/-- **Rectifying a proper homotopy inverse of a subspace inclusion to a proper strong deformation
retraction.** Suppose `A ⊆ X` has the proper homotopy extension property, its inclusion
`Subtype.val : A → X` is proper, and `g : X → A` is a proper map with jointly proper homotopies
`H : g ∘ incl ≃ id_A` on `I × A` and `K : incl ∘ g ≃ id_X` on `I × X`. Then there exist a proper
retraction `r : X → A` fixing `A` pointwise and a proper homotopy relative to `A` from `id_X` to
`incl ∘ r`. -/
theorem properStrongDeformationRetract_of_inverse (A : Set X)
    (hA : HasProperHomotopyExtensionProperty A) (hincl : IsProperMap (Subtype.val : A → X))
    (g : C(X, A)) (hg : IsProperMap g)
    (H : ContinuousMap.Homotopy (g.comp (subtypeVal A)) (ContinuousMap.id A))
    (K : ContinuousMap.Homotopy ((subtypeVal A).comp g) (ContinuousMap.id X))
    (hH : IsProperMap H) (hK : IsProperMap K) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r (a : X) = a) ∧
      ∃ H' : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H' := by
  have hA_closed : IsClosed A := by simpa only [Subtype.range_coe] using hincl.isClosed_range
  obtain ⟨r, hr_proper, hr, K_rg, hK_rg⟩ := hA.exists_proper_retraction_homotopic g hg H hH
  exact ⟨r, hr_proper, hr, hA.exists_proper_homotopyRel_of_retraction hA_closed hr
    (((Homotopy.refl (subtypeVal A)).comp K_rg).trans K)
    (Homotopy.isProperMap_trans
      (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl (f := subtypeVal A) hincl) hK_rg) hK)⟩

/-- A subset with the proper homotopy extension property is a proper strong deformation retract of
`X` if and only if its inclusion is a proper homotopy equivalence. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff
    (hA : HasProperHomotopyExtensionProperty A) :
    (∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r (a : X) = a) ∧
      ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H) ↔
      (subtypeVal A).HasProperHomotopyInverse := by
  refine ⟨fun ⟨r, hr_proper, hr, H, hH⟩ ↦ ?_, fun hinv ↦ ?_⟩
  · have hincl : IsProperMap (subtypeVal A) :=
      isProperMap_of_comp_of_surj r.continuous (subtypeVal A).continuous
        (Homotopy.isProperMap_right hH) fun a ↦ ⟨a, hr a⟩
    exact .intro hincl r hr_proper ((Homotopy.refl _).cast (ContinuousMap.ext hr).symm rfl)
      H.toHomotopy.symm
      ((Homotopy.isProperMap_cast_iff _ _).2 (Homotopy.isProperMap_refl isProperMap_id))
      (Homotopy.isProperMap_symm hH)
  · obtain ⟨g, hg, H, K, hH, hK⟩ := hinv.exists_inverse
    exact properStrongDeformationRetract_of_inverse A hA hinv.isProperMap g hg H K hH hK

end DeformationRetract

end TauCeti
