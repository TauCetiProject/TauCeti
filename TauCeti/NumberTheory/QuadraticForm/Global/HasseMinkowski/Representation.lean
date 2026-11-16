/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation
import TauCeti.NumberTheory.QuadraticForm.Global.HasseMinkowski.Isotropy

/-!
# The Hasse–Minkowski theorem for representation

Over a number field `K`, both scalar representation and representation of a finite-dimensional
quadratic form satisfy the local-to-global principle:

* **Scalar representation**: a quadratic form `Q` on an arbitrary (finite- or infinite-dimensional,
  possibly degenerate) vector space over `K` represents a scalar `a : K` if and only if it locally
  represents `a` at every finite and every real place of `K`. For `a ≠ 0`, splitting off the
  radical reduces to the quotient `Q_reg = Q.lift Q.radical le_rfl`, whose representation of `a` is
  equivalent to isotropy of `⟨-a⟩ ⊥ Q_reg` and therefore follows from
  `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic`.
* **Form representation**: a finite-dimensional quadratic form `Q` (possibly degenerate) is
  represented by an arbitrary (possibly degenerate or infinite-dimensional) quadratic form `R` if
  and only if `Q` is locally represented by `R` at every finite and every real place of `K`.
  Splitting `Q ≅ 0_{rad(Q)} ⊥ Q_reg`, the regular part `Q_reg` is handled by diagonalizing into
  lines and applying scalar Hasse–Minkowski together with local Witt cancellation. Splitting
  `Q_reg` off `R` reduces the remaining radical part to representing a finite-dimensional zero form
  `0_{K^s}`, which follows by induction on `s`: local isotropy supplies a nonzero global isotropic
  vector `v` of `R`, splitting off either a one-dimensional zero summand (if `v ∈ rad(R)`) or a
  hyperbolic plane (if `v ∉ rad(R)`), each of which reduces `s` by one at every place.

## Main results

* `QuadraticForm.represents_iff_locallyRepresentsScalar`: the **Hasse–Minkowski theorem for scalar
  representation**, for arbitrary forms and scalars (including `a = 0`, degenerate forms, and
  infinite-dimensional spaces).
* `QuadraticForm.isRepresentedBy_iff_locallyRepresents`: the **Hasse–Minkowski theorem for
  representation of quadratic forms**, for arbitrary finite-dimensional `Q` and arbitrary `R`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), Theorem 66:3.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, Corollary 1 to Theorem 8.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter VI, Corollary 3.3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Dropping a zero orthogonal summand does not change which scalars a form represents locally. -/
private theorem locallyRepresentsScalar_zero_prod_iff
    {T : Type*} [AddCommGroup T] [Module K T] (Q : _root_.QuadraticForm K V) (a : K) :
    LocallyRepresentsScalar ((0 : _root_.QuadraticForm K T).prod Q) a ↔
      Q.LocallyRepresentsScalar a := by
  rw [locallyRepresentsScalar_iff, locallyRepresentsScalar_iff]
  refine and_congr (forall_congr' fun v ↦ ?_) (forall_congr' fun wp ↦ ?_)
  · rw [(atFinitePlaceProd (0 : _root_.QuadraticForm K T) Q v).represents_iff,
      atFinitePlace_def (0 : _root_.QuadraticForm K T), baseChange_zero,
      QuadraticMap.represents_zero_prod_iff]
  · let : Algebra K ℝ := (embedding_of_isReal wp.2).toAlgebra
    rw [(atRealPlaceProd (0 : _root_.QuadraticForm K T) Q wp).represents_iff,
      atRealPlace_def (0 : _root_.QuadraticForm K T), baseChange_zero,
      QuadraticMap.represents_zero_prod_iff]

/-- **The Hasse–Minkowski theorem for scalar representation.** Over a number field `K`, a quadratic
form `Q` on an arbitrary vector space represents a scalar `a : K` if and only if it locally
represents `a` at every finite and every real place of `K`. -/
theorem represents_iff_locallyRepresentsScalar (Q : _root_.QuadraticForm K V) (a : K) :
    QuadraticMap.Represents Q a ↔ Q.LocallyRepresentsScalar a := by
  refine ⟨LocallyRepresentsScalar.of_represents, fun hloc ↦ ?_⟩
  by_cases ha : a = 0
  · subst ha
    exact QuadraticMap.represents_zero Q
  -- Split off the radical so that scalar representation becomes isotropy after adjoining `⟨-a⟩`.
  let Qreg : _root_.QuadraticForm K (V ⧸ Q.radical) := Q.lift Q.radical le_rfl
  have hsplit : ((0 : _root_.QuadraticForm K Q.radical).prod Qreg).Equivalent Q :=
    ⟨QuadraticMap.IsometryEquiv.prodRadicalLift Q⟩
  have hloc_reg : Qreg.LocallyRepresentsScalar a :=
    (locallyRepresentsScalar_zero_prod_iff Qreg a).mp
      ((QuadraticMap.Equivalent.locallyRepresentsScalar_iff hsplit a).mpr hloc)
  have hiso :
      ¬ (((-a) • (QuadraticMap.sq : _root_.QuadraticForm K K)).prod Qreg).Anisotropic :=
    (not_anisotropic_iff_isLocallyIsotropic _).mpr hloc_reg.isLocallyIsotropic_smul_sq_prod
  rw [QuadraticMap.Equivalent.anisotropic_iff ⟨QuadraticMap.IsometryEquiv.prodComm _ Qreg⟩] at hiso
  have hrep_reg : QuadraticMap.Represents Qreg a :=
    QuadraticMap.mem_unitValueSet.mp
      ((QuadraticMap.mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot Qreg
        (QuadraticMap.radical_lift_radical Q) (Units.mk0 a ha)).mpr hiso)
  exact (QuadraticMap.represents_lift_iff Q le_rfl a).mp hrep_reg

/-- Local Witt cancellation for representation: any finite-dimensional summand (regular or
degenerate) cancels from local representation of orthogonal sums. -/
private theorem locallyRepresents_of_prod_locallyRepresents_prod
    {V₀ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    {Q₀ : _root_.QuadraticForm K V₀} {Q₁ : _root_.QuadraticForm K V}
    {Q₂ : _root_.QuadraticForm K W}
    (h : LocallyRepresents (Q₀.prod Q₁) (Q₀.prod Q₂)) :
    Q₁.LocallyRepresents Q₂ := by
  obtain ⟨hfin, hreal⟩ := (locallyRepresents_iff _ _).mp h
  refine (locallyRepresents_iff Q₁ Q₂).mpr ⟨fun v ↦ ?_, fun wp ↦ ?_⟩
  · let : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hv := (QuadraticMap.Equivalent.isRepresentedBy_congr
      ⟨atFinitePlaceProd Q₀ Q₁ v⟩ ⟨atFinitePlaceProd Q₀ Q₂ v⟩).mp (hfin v)
    exact isRepresentedBy_of_prod_isRepresentedBy_prod hv
  · have hwp := (QuadraticMap.Equivalent.isRepresentedBy_congr
      ⟨atRealPlaceProd Q₀ Q₁ wp⟩ ⟨atRealPlaceProd Q₀ Q₂ wp⟩).mp (hreal wp)
    exact isRepresentedBy_of_prod_isRepresentedBy_prod hwp

omit [NumberField K] in
/-- Representing a nonzero scalar `c` gives an injective isometry from the line `⟨c⟩` into `R`. -/
private theorem isRepresentedBy_smul_sq_of_represents {R : _root_.QuadraticForm K W}
    {c : K} (hc : c ≠ 0) (hrep : QuadraticMap.Represents R c) :
    (c • (QuadraticMap.sq : _root_.QuadraticForm K K)).IsRepresentedBy R := by
  obtain ⟨v, hv⟩ := (QuadraticMap.represents_iff R c).mp hrep
  have hv0 : v ≠ 0 := fun h ↦ hc (by rw [← hv, h, map_zero])
  rw [QuadraticMap.isRepresentedBy_iff]
  refine ⟨LinearMap.toSpanSingleton K W v,
    fun t₁ t₂ h ↦ smul_left_injective K hv0 (by simpa using h), fun t ↦ ?_⟩
  simp [hv, R.map_smul, smul_eq_mul]
  ring

/-- Induction on rank: a regular diagonal form locally represented by an arbitrary quadratic form
`R` is globally represented by `R`. -/
private theorem isRepresentedBy_presentedForm_of_locallyRepresents :
    ∀ (n : ℕ) (w : Fin n → Kˣ) {W : Type w} [AddCommGroup W] [Module K W]
      {R : _root_.QuadraticForm K W},
      (presentedForm ⟨n, w⟩).LocallyRepresents R → (presentedForm ⟨n, w⟩).IsRepresentedBy R
  | 0, w, W, _, _, R, _ => by
    rw [QuadraticMap.isRepresentedBy_iff]
    refine ⟨0, fun x y _ ↦ funext fun i ↦ Fin.elim0 i, fun x ↦ ?_⟩
    rw [presentedForm_apply]
    simp
  | n + 1, w, W, _, _, R, hloc => by
    let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let c : Kˣ := w 0
    let L : _root_.QuadraticForm K K := (c : K) • QuadraticMap.sq
    let Q' : _root_.QuadraticForm K (Fin n → K) := presentedForm ⟨n, fun i ↦ w i.succ⟩
    have hcons : (L.prod Q').Equivalent (presentedForm ⟨n + 1, w⟩) :=
      ⟨presentedFormConsIsometryEquiv w⟩
    have hL_nondeg : L.Nondegenerate :=
      nondegenerate_of_span_singleton_eq_top
        ((Submodule.span_singleton_eq_top_iff K (1 : K)).mpr fun x ↦ ⟨x, by simp⟩)
        (by simp [L, c.ne_zero])
    have hloc' : LocallyRepresents (L.prod Q') R :=
      (QuadraticMap.Equivalent.locallyRepresents_congr hcons (QuadraticMap.Equivalent.refl R)).mpr
        hloc
    have hLloc : L.LocallyRepresents R :=
      (LocallyRepresents.of_isRepresentedBy (QuadraticMap.isRepresentedBy_prod_left L Q')).trans
        hloc'
    have hR_c : R.LocallyRepresentsScalar (c : K) :=
      hLloc.locallyRepresentsScalar
        (LocallyRepresentsScalar.of_represents
          ((QuadraticMap.represents_iff L (c : K)).mpr ⟨1, by simp [L]⟩))
    have hLrep : L.IsRepresentedBy R :=
      isRepresentedBy_smul_sq_of_represents c.ne_zero
        ((represents_iff_locallyRepresentsScalar R (c : K)).mpr hR_c)
    obtain ⟨P, hRsplit⟩ := hLrep.exists_equivalent_prod_restrict hL_nondeg
    have hQ'loc : Q'.LocallyRepresents (R.restrict P) :=
      locallyRepresents_of_prod_locallyRepresents_prod
        ((QuadraticMap.Equivalent.locallyRepresents_congr (QuadraticMap.Equivalent.refl _)
          hRsplit).mp hloc')
    have hQ'rep : Q'.IsRepresentedBy (R.restrict P) :=
      isRepresentedBy_presentedForm_of_locallyRepresents n (fun i ↦ w i.succ) hQ'loc
    exact (QuadraticMap.Equivalent.isRepresentedBy_congr hcons
      (QuadraticMap.Equivalent.refl R)).mp
        (((QuadraticMap.IsRepresentedBy.refl L).prod hQ'rep).trans hRsplit.symm.isRepresentedBy)

/-- A finite-dimensional totally isotropic submodule of dimension at least `s` yields a
representation of the `s`-dimensional zero form. -/
private theorem isRepresentedBy_zero_fin_of_submodule {F W' : Type*} [Field F]
    [AddCommGroup W'] [Module F W'] {R' : _root_.QuadraticForm F W'} {s : ℕ}
    (U : Submodule F W') [FiniteDimensional F U] (hs : s ≤ Module.finrank F U)
    (hU : ∀ u ∈ U, R' u = 0) :
    (0 : _root_.QuadraticForm F (Fin s → F)).IsRepresentedBy R' := by
  let b := Module.finBasis F U
  let g : (Fin s → F) →ₗ[F] U :=
    Fintype.linearCombination F fun i : Fin s ↦ b (Fin.castLE hs i)
  have hg : Function.Injective g :=
    (b.linearIndependent.comp (Fin.castLE hs)
      (Fin.castLE_injective hs)).fintypeLinearCombination_injective
  exact (QuadraticMap.isRepresentedBy_iff _ _).mpr
    ⟨U.subtype ∘ₗ g, Subtype.val_injective.comp hg, fun x ↦ hU _ (g x).2⟩

/-- Injective-projection case of hyperbolic cancellation for represented zero forms. -/
private theorem isRepresentedBy_zero_of_hyperbolicPlane_prod_of_injective_snd
    {F W' : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup W'] [Module F W']
    {R' : _root_.QuadraticForm F W'} {s : ℕ}
    (p₁ : (Fin (s + 1) → F) →ₗ[F] (Fin 2 → F)) (p₂ : (Fin (s + 1) → F) →ₗ[F] W')
    (hf0 : ∀ x, hyperbolicPlane F (p₁ x) + R' (p₂ x) = 0) (hp₂ : Function.Injective p₂) :
    (0 : _root_.QuadraticForm F (Fin s → F)).IsRepresentedBy R' := by
  let φ : (Fin (s + 1) → F) →ₗ[F] F :=
    (LinearMap.proj (R := F) (φ := fun _ : Fin 2 ↦ F) 0 -
      LinearMap.proj (R := F) (φ := fun _ : Fin 2 ↦ F) 1) ∘ₗ p₁
  have hker_ge : s ≤ Module.finrank F (LinearMap.ker φ) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hle : Module.finrank F (LinearMap.range φ) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range φ)
    simp only [Module.finrank_fin_fun] at hsum
    omega
  let q : LinearMap.ker φ →ₗ[F] W' := p₂ ∘ₗ (LinearMap.ker φ).subtype
  have hfin : Module.finrank F (LinearMap.range q) = Module.finrank F (LinearMap.ker φ) :=
    (LinearEquiv.ofInjective q (hp₂.comp Subtype.val_injective)).finrank_eq.symm
  exact isRepresentedBy_zero_fin_of_submodule (LinearMap.range q) (by omega) fun u hu ↦ by
    obtain ⟨⟨x, hx⟩, rfl⟩ := hu
    have hx0 : (p₁ x) 0 = (p₁ x) 1 := sub_eq_zero.mp hx
    have hhyp0 : hyperbolicPlane F (p₁ x) = 0 := by simp [hyperbolicPlane_apply, hx0]
    simpa [q, hhyp0] using hf0 x

/-- Non-injective-projection case of hyperbolic cancellation for represented zero forms. -/
private theorem isRepresentedBy_zero_of_hyperbolicPlane_prod_of_not_injective_snd
    {F W' : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup W'] [Module F W']
    {R' : _root_.QuadraticForm F W'} {s : ℕ}
    (f : (Fin (s + 1) → F) →ₗ[F] (Fin 2 → F) × W') (hf_inj : Function.Injective f)
    (hf0 : ∀ x, hyperbolicPlane F (f x).1 + R' (f x).2 = 0)
    (hp₂ : ¬ Function.Injective (LinearMap.snd F (Fin 2 → F) W' ∘ₗ f)) :
    (0 : _root_.QuadraticForm F (Fin s → F)).IsRepresentedBy R' := by
  let p₁ : (Fin (s + 1) → F) →ₗ[F] (Fin 2 → F) := LinearMap.fst F _ _ ∘ₗ f
  let p₂ : (Fin (s + 1) → F) →ₗ[F] W' := LinearMap.snd F _ _ ∘ₗ f
  have hf0' : ∀ x, hyperbolicPlane F (p₁ x) + R' (p₂ x) = 0 := hf0
  have hzero_of : ∀ x, p₂ x = 0 → (p₁ x) 0 = 0 → (p₁ x) 1 = 0 → x = 0 := fun x hx2 hx0 hx1 ↦
    hf_inj (by rw [map_zero]; refine Prod.ext (funext fun i ↦ ?_) hx2; fin_cases i <;> assumption)
  obtain ⟨x₀, hx₀_ker, hx₀⟩ : ∃ x₀, p₂ x₀ = 0 ∧ x₀ ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hp₂; simpa [p₂, not_forall] using hp₂
  set a₀ : F := (p₁ x₀) 0; set b₀ : F := (p₁ x₀) 1
  have hab : a₀ = b₀ ∨ a₀ = -b₀ := sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp
    (by simpa [hyperbolicPlane_apply, a₀, b₀, hx₀_ker] using hf0' x₀))
  have ha₀ : a₀ ≠ 0 := fun ha ↦
    hx₀ (hzero_of x₀ hx₀_ker ha (by rcases hab with h | h <;> simpa [ha] using h.symm))
  have hhyp_all : ∀ x, (p₁ x) 0 ^ 2 = (p₁ x) 1 ^ 2 := fun x ↦ by
    have h1 := hf0' (x₀ + x); rw [map_add p₁, map_add p₂, hx₀_ker, zero_add] at h1
    have h0 : hyperbolicPlane F (p₁ x₀) = 0 := by simpa [hx₀_ker] using hf0' x₀
    have hp : QuadraticMap.polar (hyperbolicPlane F) (p₁ x₀) (p₁ x) = 0 := by
      rw [QuadraticMap.polar]; linear_combination h1 - h0 - hf0' x
    rw [polar_hyperbolicPlane] at hp
    have hpol : a₀ * (p₁ x) 0 = b₀ * (p₁ x) 1 :=
      sub_eq_zero.mp ((isUnit_of_invertible (2 : F)).mul_right_eq_zero.mp hp)
    rcases hab with hab | hab
    · rw [← hab] at hpol; rw [mul_left_cancel₀ ha₀ hpol]
    · have hneg : a₀ * (p₁ x) 0 = a₀ * -(p₁ x) 1 := by linear_combination hpol + (p₁ x) 1 * hab
      rw [mul_left_cancel₀ ha₀ hneg, neg_sq]
  have hker_le : Module.finrank F (LinearMap.ker p₂) ≤ 1 := by
    let ψ : LinearMap.ker p₂ →ₗ[F] F :=
      LinearMap.proj (R := F) (φ := fun _ : Fin 2 ↦ F) 0 ∘ₗ p₁ ∘ₗ (LinearMap.ker p₂).subtype
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]; rintro ⟨x, hx⟩ hx0; apply Subtype.ext
      exact hzero_of x hx hx0
        (by have := hhyp_all x; simpa [show (p₁ x) 0 = 0 from hx0] using this.symm)
    simpa using LinearMap.finrank_le_finrank_of_injective hψ
  have hrange_ge : s ≤ Module.finrank F (LinearMap.range p₂) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker p₂
    simp only [Module.finrank_fin_fun] at hsum; omega
  exact isRepresentedBy_zero_fin_of_submodule (LinearMap.range p₂) hrange_ge fun u hu ↦ by
    obtain ⟨x, rfl⟩ := hu
    have h0 : hyperbolicPlane F (p₁ x) = 0 := by rw [hyperbolicPlane_apply, hhyp_all x, sub_self]
    simpa [h0] using hf0' x

/-- Splitting off a hyperbolic plane reduces the dimension of a represented zero form by at most
one. -/
private theorem isRepresentedBy_zero_of_isRepresentedBy_hyperbolicPlane_prod
    {F W' : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup W'] [Module F W']
    {R' : _root_.QuadraticForm F W'} {s : ℕ}
    (h : (0 : _root_.QuadraticForm F (Fin (s + 1) → F)).IsRepresentedBy
      ((hyperbolicPlane F).prod R')) :
    (0 : _root_.QuadraticForm F (Fin s → F)).IsRepresentedBy R' := by
  obtain ⟨f, hf_inj, hf_map⟩ := (QuadraticMap.isRepresentedBy_iff _ _).mp h
  have hf0 : ∀ x, hyperbolicPlane F (f x).1 + R' (f x).2 = 0 := fun x ↦ by simpa using hf_map x
  by_cases hp₂ : Function.Injective (LinearMap.snd F (Fin 2 → F) W' ∘ₗ f)
  · exact isRepresentedBy_zero_of_hyperbolicPlane_prod_of_injective_snd
      (LinearMap.fst F _ _ ∘ₗ f) (LinearMap.snd F _ _ ∘ₗ f) hf0 hp₂
  · exact isRepresentedBy_zero_of_hyperbolicPlane_prod_of_not_injective_snd f hf_inj hf0 hp₂

private theorem equivalent_atFinitePlace_zero_fin (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace (0 : _root_.QuadraticForm K (Fin n → K)) v).Equivalent
      (0 : _root_.QuadraticForm (v.adicCompletion K) (Fin n → v.adicCompletion K)) := by
  rw [atFinitePlace_def, baseChange_zero]
  exact ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp), map_app' := fun _ ↦ rfl }⟩

private theorem equivalent_atRealPlace_zero_fin (n : ℕ) (wp : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace (0 : _root_.QuadraticForm K (Fin n → K)) wp).Equivalent
      (0 : _root_.QuadraticForm ℝ (Fin n → ℝ)) := by
  let : Algebra K ℝ := (embedding_of_isReal wp.2).toAlgebra
  rw [atRealPlace_def, baseChange_zero]
  exact ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp), map_app' := fun _ ↦ rfl }⟩

private theorem equivalent_atFinitePlace_hyperbolicPlane (v : HeightOneSpectrum (𝓞 K)) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    (atFinitePlace (hyperbolicPlane K) v).Equivalent (hyperbolicPlane (v.adicCompletion K)) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Invertible (2 : v.adicCompletion K) :=
    (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  have hhypK : hyperbolicPlane K = QuadraticMap.weightedSumSquares K ![(1 : K), -1] := by
    ext x
    simp [hyperbolicPlane_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, pow_two,
      sub_eq_add_neg]
  rw [hhypK]
  refine ⟨(atFinitePlaceWeightedSumSquares v ![(1 : K), -1]).trans
    { toLinearEquiv := LinearEquiv.refl _ _, map_app' := fun x ↦ ?_ }⟩
  simp [hyperbolicPlane_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, pow_two,
    sub_eq_add_neg]

private theorem equivalent_atRealPlace_hyperbolicPlane (wp : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    (atRealPlace (hyperbolicPlane K) wp).Equivalent (hyperbolicPlane ℝ) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hhypK : hyperbolicPlane K = QuadraticMap.weightedSumSquares K ![(1 : K), -1] := by
    ext x
    simp [hyperbolicPlane_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, pow_two,
      sub_eq_add_neg]
  rw [hhypK]
  refine ⟨(atRealPlaceWeightedSumSquares wp ![(1 : K), -1]).trans
    { toLinearEquiv := LinearEquiv.refl _ _, map_app' := fun x ↦ ?_ }⟩
  simp [hyperbolicPlane_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, pow_two,
    sub_eq_add_neg]

/-- Local version of hyperbolic cancellation for represented zero forms. -/
private theorem locallyRepresents_zero_of_locallyRepresents_hyperbolicPlane_prod
    {s : ℕ} {R' : _root_.QuadraticForm K W}
    (h : letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
      (0 : _root_.QuadraticForm K (Fin (s + 1) → K)).LocallyRepresents
        ((hyperbolicPlane K).prod R')) :
    (0 : _root_.QuadraticForm K (Fin s → K)).LocallyRepresents R' := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨hfin, hreal⟩ := (locallyRepresents_iff _ _).mp h
  refine (locallyRepresents_iff _ _).mpr ⟨fun v ↦ ?_, fun wp ↦ ?_⟩
  · let : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hv := (QuadraticMap.Equivalent.isRepresentedBy_congr
      (equivalent_atFinitePlace_zero_fin (s + 1) v)
      (QuadraticMap.Equivalent.trans ⟨atFinitePlaceProd _ R' v⟩
        ((equivalent_atFinitePlace_hyperbolicPlane v).prod (QuadraticMap.Equivalent.refl _)))).mp
      (hfin v)
    exact (QuadraticMap.Equivalent.isRepresentedBy_congr (equivalent_atFinitePlace_zero_fin s v)
      (QuadraticMap.Equivalent.refl _)).mpr
        (isRepresentedBy_zero_of_isRepresentedBy_hyperbolicPlane_prod hv)
  · have hwp := (QuadraticMap.Equivalent.isRepresentedBy_congr
      (equivalent_atRealPlace_zero_fin (s + 1) wp)
      (QuadraticMap.Equivalent.trans ⟨atRealPlaceProd _ R' wp⟩
        ((equivalent_atRealPlace_hyperbolicPlane wp).prod (QuadraticMap.Equivalent.refl _)))).mp
      (hreal wp)
    exact (QuadraticMap.Equivalent.isRepresentedBy_congr (equivalent_atRealPlace_zero_fin s wp)
      (QuadraticMap.Equivalent.refl _)).mpr
        (isRepresentedBy_zero_of_isRepresentedBy_hyperbolicPlane_prod hwp)

omit [NumberField K] in
/-- A nonzero radical vector splits a one-dimensional zero summand off `R`. -/
private theorem exists_equivalent_zero_prod_of_mem_radical {R : _root_.QuadraticForm K W}
    {v : W} (hv0 : v ≠ 0) (hvrad : v ∈ R.radical) :
    ∃ U : Submodule K W, R.Equivalent ((0 : _root_.QuadraticForm K K).prod (R.restrict U)) := by
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (Submodule.span K {v})
  let e : ((0 : _root_.QuadraticForm K K).prod (R.restrict U)).IsometryEquiv R :=
    { toLinearEquiv := (LinearEquiv.toSpanNonzeroSingleton K W v hv0).prodCongr
        (LinearEquiv.refl K U) |>.trans (Submodule.prodEquivOfIsCompl _ U hU)
      map_app' := fun ⟨t, u⟩ ↦ by
        have htv : t • v ∈ R.radical := Submodule.smul_mem R.radical t hvrad
        have hmem := QuadraticMap.mem_radical_iff'.mp htv
        simpa using hmem.2 u.1 }
  exact ⟨U, ⟨e.symm⟩⟩

omit [NumberField K] in
/-- A non-radical isotropic vector has an isotropic partner with polar pairing one. -/
private theorem exists_isotropic_polar_eq_one_of_not_mem_radical {R : _root_.QuadraticForm K W}
    {v : W} (hvQ : R v = 0) (hvrad : v ∉ R.radical) :
    ∃ y : W, R y = 0 ∧ QuadraticMap.polar R v y = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, QuadraticMap.polar R v w ≠ 0 := by
    by_contra h
    push Not at h
    apply hvrad
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hvQ, fun z ↦ ?_⟩
    rw [QuadraticMap.map_add R, hvQ, h z, zero_add, add_zero]
  let z := (QuadraticMap.polar R v w)⁻¹ • w
  have hvz : QuadraticMap.polar R v z = 1 := by simp [z, QuadraticMap.polar_smul_right, hw]
  refine ⟨z - R z • v, ?_, ?_⟩
  · simp [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add, R.map_smul, hvQ,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_comm R z v, hvz, smul_eq_mul]
  · simp [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_self,
      hvQ, hvz]

/-- Induction on dimension: a finite-dimensional zero form locally represented by an arbitrary
quadratic form `R` is globally represented by `R`. -/
private theorem isRepresentedBy_zero_fin_of_locallyRepresents :
    ∀ (s : ℕ) {W : Type w} [AddCommGroup W] [Module K W] {R : _root_.QuadraticForm K W},
      (0 : _root_.QuadraticForm K (Fin s → K)).LocallyRepresents R →
        (0 : _root_.QuadraticForm K (Fin s → K)).IsRepresentedBy R
  | 0, W, _, _, R, _ =>
    (QuadraticMap.isRepresentedBy_iff _ _).mpr
      ⟨0, fun _ _ _ ↦ funext fun i ↦ Fin.elim0 i, fun _ ↦ by simp⟩
  | s + 1, W, _, _, R, hloc => by
    let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have hzero_iso : ¬ (0 : _root_.QuadraticForm K (Fin (s + 1) → K)).Anisotropic :=
      (QuadraticMap.not_anisotropic_iff_exists _).mpr
        ⟨fun _ ↦ 1, fun h ↦ one_ne_zero (congrFun h 0), rfl⟩
    have hRiso : ¬ R.Anisotropic := (not_anisotropic_iff_isLocallyIsotropic R).mpr
      (hloc.isLocallyIsotropic (isLocallyIsotropic_of_not_anisotropic _ hzero_iso))
    obtain ⟨v, hv0, hvQ⟩ := (QuadraticMap.not_anisotropic_iff_exists R).mp hRiso
    have hsplit0 : (0 : _root_.QuadraticForm K (Fin (s + 1) → K)).Equivalent
        ((0 : _root_.QuadraticForm K K).prod (0 : _root_.QuadraticForm K (Fin s → K))) :=
      ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_prod, add_comm])
         map_app' := fun _ ↦ by simp }⟩
    by_cases hvrad : v ∈ R.radical
    · obtain ⟨U, hRU⟩ := exists_equivalent_zero_prod_of_mem_radical hv0 hvrad
      have hloc_s : (0 : _root_.QuadraticForm K (Fin s → K)).LocallyRepresents (R.restrict U) :=
        locallyRepresents_of_prod_locallyRepresents_prod
          ((QuadraticMap.Equivalent.locallyRepresents_congr hsplit0 hRU).mp hloc)
      have hrep_s := isRepresentedBy_zero_fin_of_locallyRepresents s hloc_s
      exact (QuadraticMap.Equivalent.isRepresentedBy_congr hsplit0 hRU).mpr
        ((QuadraticMap.IsRepresentedBy.refl _).prod hrep_s)
    · obtain ⟨y, hyQ, hvy⟩ := exists_isotropic_polar_eq_one_of_not_mem_radical hvQ hvrad
      have hRH := R.equivalent_hyperbolicPlane_prod_restrict_orthogonal hvQ hyQ hvy
      have hloc_s : (0 : _root_.QuadraticForm K (Fin s → K)).LocallyRepresents
          (R.restrict (LinearMap.BilinForm.orthogonal R.polarBilin (Submodule.span K {v, y}))) :=
        locallyRepresents_zero_of_locallyRepresents_hyperbolicPlane_prod
          ((QuadraticMap.Equivalent.locallyRepresents_congr (QuadraticMap.Equivalent.refl _)
            hRH).mp hloc)
      have hrep_s := isRepresentedBy_zero_fin_of_locallyRepresents s hloc_s
      have h0H : (0 : _root_.QuadraticForm K K).IsRepresentedBy (hyperbolicPlane K) :=
        (QuadraticMap.isRepresentedBy_iff _ _).mpr
          ⟨LinearMap.pi ![LinearMap.id, LinearMap.id],
            fun _ _ h ↦ congrFun h 0, fun t ↦ by simp [hyperbolicPlane_apply]⟩
      exact (QuadraticMap.Equivalent.isRepresentedBy_congr hsplit0 hRH).mpr (h0H.prod hrep_s)

/-- **The Hasse–Minkowski theorem for representation of quadratic forms.** Over a number field `K`,
a finite-dimensional quadratic form `Q` is represented by an arbitrary quadratic form `R` if and
only if `Q` is locally represented by `R` at every finite and every real place of `K`. Neither
nondegeneracy of `Q` or `R` nor finite dimensionality of `R` is required. -/
theorem isRepresentedBy_iff_locallyRepresents [FiniteDimensional K V]
    (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W) :
    Q.IsRepresentedBy R ↔ Q.LocallyRepresents R := by
  refine ⟨LocallyRepresents.of_isRepresentedBy, fun hloc ↦ ?_⟩
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let s := Module.finrank K Q.radical
  let Qreg : _root_.QuadraticForm K (V ⧸ Q.radical) := Q.lift Q.radical le_rfl
  obtain ⟨⟨n, w⟩, hQw⟩ := exists_presentedForm_equivalent Qreg Q.nondegenerate_lift_radical
  have hrad : (0 : _root_.QuadraticForm K Q.radical).Equivalent
      (0 : _root_.QuadraticForm K (Fin s → K)) :=
    ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp [s]), map_app' := fun _ ↦ rfl }⟩
  have hQsplit : Q.Equivalent ((presentedForm ⟨n, w⟩).prod
      (0 : _root_.QuadraticForm K (Fin s → K))) :=
    QuadraticMap.Equivalent.trans
      ⟨(QuadraticMap.IsometryEquiv.prodRadicalLift Q).symm⟩
      ((hrad.prod hQw).trans ⟨QuadraticMap.IsometryEquiv.prodComm _ _⟩)
  have hloc' : LocallyRepresents
      ((presentedForm ⟨n, w⟩).prod (0 : _root_.QuadraticForm K (Fin s → K))) R :=
    (QuadraticMap.Equivalent.locallyRepresents_congr hQsplit
      (QuadraticMap.Equivalent.refl R)).mp hloc
  have hreg_rep : (presentedForm ⟨n, w⟩).IsRepresentedBy R :=
    isRepresentedBy_presentedForm_of_locallyRepresents n w
      ((LocallyRepresents.of_isRepresentedBy (QuadraticMap.isRepresentedBy_prod_left _ _)).trans
        hloc')
  obtain ⟨P, hRsplit⟩ := hreg_rep.exists_equivalent_prod_restrict (nondegenerate_presentedForm _)
  have h0_loc : (0 : _root_.QuadraticForm K (Fin s → K)).LocallyRepresents (R.restrict P) :=
    locallyRepresents_of_prod_locallyRepresents_prod
      ((QuadraticMap.Equivalent.locallyRepresents_congr (QuadraticMap.Equivalent.refl _)
        hRsplit).mp hloc')
  have h0_rep := isRepresentedBy_zero_fin_of_locallyRepresents s h0_loc
  exact (QuadraticMap.Equivalent.isRepresentedBy_congr hQsplit hRsplit).mpr
    ((QuadraticMap.IsRepresentedBy.refl _).prod h0_rep)

end QuadraticForm
