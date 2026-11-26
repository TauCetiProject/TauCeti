/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic
import TauCeti.NumberTheory.QuadraticForm.Global.Cancellation
import TauCeti.NumberTheory.QuadraticForm.Global.Isotropy

/-!
# The Hasse–Minkowski theorem for quadratic forms over number fields

Let `K` be a number field in any universe. Building on the local-to-global principles for isotropy
and scalar representation proved in `TauCeti.NumberTheory.QuadraticForm.Global.Isotropy`, this file
proves the Hasse–Minkowski theorems for representation of forms and for isometry over `K`, with no
nondegeneracy hypothesis on any form:

* **Form representation** (O'Meara 66:3): a quadratic form `Q` admits an injective isometry into a
  quadratic form `R` on a finite-dimensional space if and only if it does so at every finite and
  every real place (finite-dimensionality of the domain of `Q` follows from local representation).
* **Isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3): a quadratic form `Q` is
  isometric over `K` to a quadratic form `R` on a finite-dimensional space if and only if they are
  isometric at every finite and every real place (finite-dimensionality of the domain of `Q`
  follows from local equivalence).

## Proof outline

Representation of a regular form `Q` by a regular form `R` proceeds by induction on the dimension
of `Q`, splitting off a common nonzero value `⟨c⟩` and applying Witt cancellation for
representation (`TauCeti.isRepresentedBy_of_prod_isRepresentedBy_prod`) at each place. For
arbitrary forms `Q` and `R`, splitting off their radicals reduces first to embedding the regular
part of `Q` into the regular part of `R` (with regular complement `S`), then cancelling that
regular part locally to embed the radical of `Q` into `R.radical ⊥ S`; the excess radical
dimension embeds into `S` by induction on the Witt index via isotropy and hyperbolic-plane
splitting. Finally, isometry follows immediately from form representation between spaces of equal
finite dimension (`QuadraticForm.LocallyEquivalent.finrank_eq`).

## Main results

* `QuadraticForm.LocallyRepresents.isRepresentedBy`,
  `QuadraticForm.isRepresentedBy_iff_locallyRepresents`: Hasse–Minkowski for representation of
  forms.
* `QuadraticForm.LocallyEquivalent.equivalent`,
  `QuadraticForm.equivalent_iff_locallyEquivalent`: Hasse–Minkowski for isometry.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:3 and 66:4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Proposition 3.7 and Theorem 6.3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti
open scoped TensorProduct

universe u v w

namespace QuadraticForm

section Representation

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3), when both forms are
regular, proved by induction on the dimension of the represented form. -/
private theorem isRepresentedBy_of_locallyRepresents_of_nondegenerate_aux :
    ∀ n : ℕ, ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W},
      Module.finrank K V = n → Q.Nondegenerate → R.Nondegenerate →
      Q.LocallyRepresents R → Q.IsRepresentedBy R := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ W _ _ _ Q R hV _ _ _
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    exact (isRepresentedBy_iff Q R).mpr
      ⟨0, Function.injective_of_subsingleton _, fun x => by simp [Subsingleton.elim x 0]⟩
  | succ n ih =>
    intro V _ _ _ W _ _ _ Q R hV hQ hR hloc
    let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨v₀, hv₀⟩ := hQ.exists_isUnit
    set c : K := Q v₀
    have hc : c ≠ 0 := hv₀.ne_zero
    let L : _root_.QuadraticForm K K := c • QuadraticMap.sq
    have hline_nd : L.Nondegenerate := nondegenerate_smul_sq hc
    have hR_c : Represents R c :=
      (represents_iff_locallyRepresentsScalar R c).mpr
        (hloc.locallyRepresentsScalar
          (LocallyRepresentsScalar.of_represents ((represents_iff Q c).mpr ⟨v₀, rfl⟩)))
    -- Split `⟨c⟩` off both `Q` and `R` with regular complements `Q|_P` and `R|_S`.
    obtain ⟨P, hP, hQP⟩ :=
      (((represents_iff Q c).mpr ⟨v₀, rfl⟩).isRepresentedBy_smul_sq hc).exists_equivalent_prod
        hline_nd hQ
    obtain ⟨S, hS, hRS⟩ :=
      (hR_c.isRepresentedBy_smul_sq hc).exists_equivalent_prod hline_nd hR
    let QP : _root_.QuadraticForm K P := Q.restrict P
    let RS : _root_.QuadraticForm K S := R.restrict S
    have hPrank : Module.finrank K P = n := by
      obtain ⟨e⟩ := hQP
      have hdim := e.toLinearEquiv.finrank_eq
      rw [hV, Module.finrank_prod, Module.finrank_self] at hdim
      omega
    have hPS_loc : QP.LocallyRepresents RS :=
      locallyRepresents_of_prod_locallyRepresents_prod hline_nd <|
        (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr hQP hRS).mp hloc
    have hprod_rep : (L.prod QP).IsRepresentedBy (L.prod RS) :=
      (IsRepresentedBy.refl L).prod (ih hPrank hP hS hPS_loc)
    exact (hQP.isRepresentedBy_congr hRS).mpr hprod_rep

/-- A zero form on `Fin k → K` that is locally represented by a diagonal regular form is globally
represented by it, proved by induction on `k` via isotropy and hyperbolic-plane splitting. -/
private theorem zero_fin_isRepresentedBy_presentedForm :
    ∀ k : ℕ, ∀ (p : RegularFormPresentation K),
      LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm p) →
      (0 : _root_.QuadraticForm K (Fin k → K)).IsRepresentedBy (presentedForm p) := by
  intro k
  induction k with
  | zero =>
    intro p _
    exact (isRepresentedBy_iff _ _).mpr
      ⟨0, Function.injective_of_subsingleton _, fun x => by simp [Subsingleton.elim x 0]⟩
  | succ k ih =>
    intro p hloc
    let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have hzero_iso : ¬(0 : _root_.QuadraticForm K (Fin (k + 1) → K)).Anisotropic := by
      rw [not_anisotropic_iff_exists]
      refine ⟨Pi.single 0 1, fun h0 => ?_, rfl⟩
      have h1 := congrFun h0 0; simp at h1
    have hp_iso : ¬(presentedForm p).Anisotropic :=
      not_anisotropic_of_isLocallyIsotropic
        (hloc.isLocallyIsotropic (isLocallyIsotropic_of_not_anisotropic _ hzero_iso))
    obtain ⟨q, hq⟩ :=
      exists_hyperbolicPlane_prod_equivalent (presentedForm p) (nondegenerate_presentedForm p)
        hp_iso
    have hprod_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin (k + 1) → K))
        ((hyperbolicPlane K).prod (presentedForm q)) :=
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl _) hq).mp hloc
    have hq_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm q) := by
      refine (locallyRepresents_iff _ _).mpr ⟨fun v => ?_, fun w => ?_⟩
      · rw [atFinitePlace_def, atFinitePlace_def]
        exact zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).1 v)
          (by simp)
      · let _ : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).2 w)
          (by simp)
    have hline_rep : (0 : _root_.QuadraticForm K K).IsRepresentedBy (hyperbolicPlane K) := by
      simpa using isRepresentedBy_smul_sq_of_apply_eq (Q := hyperbolicPlane K) (x := ![1, 1])
        (c := 0) (by simp [hyperbolicPlane_apply])
        (by intro h; have h0 := congrFun h 0; simp at h0)
    have hprod_rep : ((0 : _root_.QuadraticForm K K).prod
        (0 : _root_.QuadraticForm K (Fin k → K))).IsRepresentedBy
        ((hyperbolicPlane K).prod (presentedForm q)) :=
      hline_rep.prod (ih q hq_loc)
    have hzero_split : (0 : _root_.QuadraticForm K (Fin (k + 1) → K)).Equivalent
        ((0 : _root_.QuadraticForm K K).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (K × (Fin k → K))
           map_app' := fun _ => by simp }⟩
    exact (hzero_split.isRepresentedBy_congr hq).mpr hprod_rep

/-- A zero form locally represented by `0_Z ⊥ T` (with `T` regular) is globally represented by
`0_Z ⊥ T`. -/
private theorem zero_isRepresentedBy_zero_prod_of_locallyRepresents
    {U : Type v} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {Z : Type w} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    {M : Type w} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {T : _root_.QuadraticForm K M} (hT : T.Nondegenerate)
    (hloc : LocallyRepresents (0 : _root_.QuadraticForm K U)
      ((0 : _root_.QuadraticForm K Z).prod T)) :
    (0 : _root_.QuadraticForm K U).IsRepresentedBy ((0 : _root_.QuadraticForm K Z).prod T) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  by_cases hle : Module.finrank K U ≤ Module.finrank K Z
  · exact (zero_isRepresentedBy_zero_of_finrank_le hle).trans (isRepresentedBy_prod_left _ T)
  · set k := Module.finrank K U - Module.finrank K Z
    have hk : k + Module.finrank K Z = Module.finrank K U := Nat.sub_add_cancel (by omega)
    have hT_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) T := by
      refine (locallyRepresents_iff _ T).mpr ⟨fun v => ?_, fun w => ?_⟩
      · rw [atFinitePlace_def, atFinitePlace_def]
        exact zero_baseChange_isRepresentedBy_of_zero_prod
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hloc).1 v)
          (by simp [hk])
      · let _ : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_baseChange_isRepresentedBy_of_zero_prod
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hloc).2 w)
          (by simp [hk])
    obtain ⟨p, hp⟩ := exists_presentedForm_equivalent T hT
    have hp_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm p) :=
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl _) hp).mp hT_loc
    have hT_rep : (0 : _root_.QuadraticForm K (Fin k → K)).IsRepresentedBy T :=
      (zero_fin_isRepresentedBy_presentedForm k p hp_loc).trans hp.symm.isRepresentedBy
    have hsplit : (0 : _root_.QuadraticForm K U).Equivalent
        ((0 : _root_.QuadraticForm K Z).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (Z × (Fin k → K))
           map_app' := fun _ => by simp }⟩
    exact hsplit.isRepresentedBy.trans ((IsRepresentedBy.refl _).prod hT_rep)

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3): a quadratic form over a
number field is represented by a finite-dimensional quadratic form `R` if it is locally represented
by `R` at every finite and every real place. No nondegeneracy hypothesis is needed on either form,
and finite-dimensionality of `V` follows from local representation. -/
theorem LocallyRepresents.isRepresentedBy {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyRepresents R) :
    Q.IsRepresentedBy R := by
  have : FiniteDimensional K V := finiteDimensional_of_locallyRepresents h
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨C₁, -, hC₁, hQe⟩ := Q.exists_equivalent_zero_radical_prod
  obtain ⟨C₂, -, hC₂, hRe⟩ := R.exists_equivalent_zero_radical_prod
  let Q₁ : _root_.QuadraticForm K C₁ := Q.restrict C₁
  let R₂ : _root_.QuadraticForm K C₂ := R.restrict C₂
  -- Step 1: embed the regular part `Q₁` of `Q` into the regular part `R₂` of `R`.
  have hQ₁_zero_loc : Q₁.LocallyRepresents ((0 : _root_.QuadraticForm K R.radical).prod R₂) :=
    (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl Q₁) hRe).mp
      ((LocallyRepresents.of_isRepresentedBy (restrict_isRepresentedBy Q C₁)).trans h)
  have hQ₁R₂_loc : Q₁.LocallyRepresents R₂ := by
    refine (locallyRepresents_iff Q₁ R₂).mpr ⟨fun v => ?_, fun w => ?_⟩
    · rw [atFinitePlace_def, atFinitePlace_def]
      exact baseChange_isRepresentedBy_of_zero_prod hC₁
        (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hQ₁_zero_loc).1 v)
    · let _ : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
      rw [atRealPlace_def, atRealPlace_def]
      exact baseChange_isRepresentedBy_of_zero_prod hC₁
        (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hQ₁_zero_loc).2 w)
  have hQ₁R₂ : Q₁.IsRepresentedBy R₂ :=
    isRepresentedBy_of_locallyRepresents_of_nondegenerate_aux
      (Module.finrank K C₁) rfl hC₁ hC₂ hQ₁R₂_loc
  -- Step 2: split `Q₁` off `R₂`, cancel `Q₁` locally, and embed `Q.radical` into `R.radical ⊥ S`.
  obtain ⟨S, hS, hR₂S⟩ := hQ₁R₂.exists_equivalent_prod hC₁ hC₂
  let R_S : _root_.QuadraticForm K S := R₂.restrict S
  have hQ_split : Q.Equivalent (Q₁.prod (0 : _root_.QuadraticForm K Q.radical)) :=
    hQe.trans ⟨IsometryEquiv.prodComm _ Q₁⟩
  have hR_split : R.Equivalent (Q₁.prod ((0 : _root_.QuadraticForm K R.radical).prod R_S)) :=
    hRe.trans <| ((Equivalent.refl _).prod hR₂S).trans <|
      ⟨(IsometryEquiv.prodAssoc _ Q₁ R_S).symm.trans <|
        ((IsometryEquiv.prodComm _ Q₁).prod (.refl R_S)).trans <|
          IsometryEquiv.prodAssoc Q₁ _ R_S⟩
  have hrad_loc : LocallyRepresents (0 : _root_.QuadraticForm K Q.radical)
      ((0 : _root_.QuadraticForm K R.radical).prod R_S) :=
    locallyRepresents_of_prod_locallyRepresents_prod hC₁ <|
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr hQ_split hR_split).mp h
  have hprod_rep : (Q₁.prod (0 : _root_.QuadraticForm K Q.radical)).IsRepresentedBy
      (Q₁.prod ((0 : _root_.QuadraticForm K R.radical).prod R_S)) :=
    (IsRepresentedBy.refl Q₁).prod (zero_isRepresentedBy_zero_prod_of_locallyRepresents hS hrad_loc)
  exact (hQ_split.isRepresentedBy_congr hR_split).mpr hprod_rep

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3): a quadratic form `Q`
over a number field admits an injective isometry into a finite-dimensional quadratic form `R` if
and only if it does so at every finite and every real place. No nondegeneracy hypothesis is needed
on either form, and finite-dimensionality of `V` follows from local representation. -/
theorem isRepresentedBy_iff_locallyRepresents (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) :
    Q.IsRepresentedBy R ↔ Q.LocallyRepresents R :=
  ⟨LocallyRepresents.of_isRepresentedBy, LocallyRepresents.isRepresentedBy⟩

/-- **Hasse–Minkowski theorem for isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3):
two quadratic forms over a number field, with target space finite-dimensional, that are isometric at
every finite and every real place are isometric over `K` (finite-dimensionality of `V` follows from
local equivalence). No nondegeneracy hypothesis is needed. -/
theorem LocallyEquivalent.equivalent {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) : Q.Equivalent R := by
  have : FiniteDimensional K V := finiteDimensional_of_locallyRepresents h.locallyRepresents
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff Q R).mp h.locallyRepresents.isRepresentedBy
  exact ⟨{ toLinearEquiv := LinearEquiv.ofBijective f
             ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.finrank_eq).mp hf⟩
           map_app' := hfQ }⟩

/-- **Hasse–Minkowski theorem for isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3):
two quadratic forms over a number field, with target space finite-dimensional, are isometric if and
only if they are isometric at every finite and every real place (finite-dimensionality of `V`
follows from local equivalence). No nondegeneracy hypothesis is needed. -/
theorem equivalent_iff_locallyEquivalent (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent, LocallyEquivalent.equivalent⟩

end Representation

end QuadraticForm
