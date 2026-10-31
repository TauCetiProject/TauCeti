/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Henselian.Idempotent
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import TauCeti.RingTheory.Henselian.Factorization

/-!
# Idempotents of integral algebras over a Henselian pair

Let `(R, I)` be a Henselian pair and let `S` be an integral `R`-algebra, for instance a finite
one. Then every idempotent of `S ⧸ IS` lifts to an idempotent of `S`
(`TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem_map_of_isIntegral`), and the lift is
unique, so reduction modulo `IS` is a bijection on idempotents. Conversely, if `I` lies in the
Jacobson radical and idempotents lift along `I` in every finite `R`-algebra, then `(R, I)` is
Henselian. This characterises Henselian pairs by their finite algebras, and it shows that `(S, IS)`
is again a Henselian pair for every integral `R`-algebra `S`.

## Main results

* `TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem_map_of_isIntegral`: over a Henselian
  pair `(R, I)`, idempotents of `S ⧸ IS` lift to `S` for every integral `R`-algebra `S`.
* `TauCeti.HenselianRing.bijOn_quotient_mk_map_isIdempotentElem`: reduction modulo `IS` is a
  bijection on idempotents.
* `TauCeti.henselianRing_of_forall_adjoinRoot`: a pair `(R, I)` with `I` in the Jacobson radical
  is Henselian if idempotents lift along `I` in `R[X]/(f)` for every monic `f`.
* `TauCeti.henselianRing_iff_forall_bijOn_isIdempotentElem`: `(R, I)` is Henselian if and only if
  reduction modulo `IS` is a bijection on idempotents for every finite `R`-algebra `S` in the
  universe of `R`.
* `TauCeti.HenselianRing.henselianRing_map_of_isIntegral`: if `(R, I)` is Henselian and `S` is an
  integral `R`-algebra, then `(S, IS)` is Henselian.

## Implementation notes

To lift an idempotent `s` modulo `IS`: the element `s² - s` lies in `IS`, so it is a root of a
monic polynomial `q ≡ Xᵈ (mod I)`. Then `s` is a root of the monic polynomial
`P = q(X² - X) · (X² - X)`, which is `Xᵈ⁺¹ (X - 1)ᵈ⁺¹` modulo `I`. This factorization into coprime
monic polynomials lifts to `P = g h` with `a g + b h = 1`, and `a(s) g(s)` is the idempotent
lifting `s`. The special case of an idempotent cutting out a summand that is cyclic modulo `I`,
`TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem_map`, has a direct proof by Hensel's
lemma; it is an input to the lifting of sections of étale algebras, on which the lifting of
factorizations used here rests.

For the converse, a simple root `a₀` modulo `I` of a monic `f` gives an idempotent of `R[X]/(f)`
modulo `I` cutting out the factor `R[X]/(X - a₀)`. Its lift `e` spans `e R[X]/(f) = R e` by
Nakayama's lemma, and `X e = a e` for a root `a` of `f`. The `R`-module `R e` is projective, being
a direct summand of `R[X]/(f)`, and this forces it to be free on `e`.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), conditions (1),
  (3) and (4).
* [Stacks Project, Lemma 15.11.8](https://stacks.math.columbia.edu/tag/09XK).
-/

public section

universe u

open Polynomial

namespace TauCeti

namespace HenselianRing

variable {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
  {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- **Idempotents lift along a Henselian pair in integral algebras.** If `(R, I)` is Henselian, `S`
is an integral `R`-algebra and `s : S` is idempotent modulo `IS`, then some idempotent of `S` is
congruent to `s` modulo `IS`. -/
@[stacks 09XI "(1) ⇒ (4), existence of lifts"]
theorem exists_isIdempotentElem_sub_mem_map_of_isIntegral {s : S}
    (hs : s * s - s ∈ I.map (algebraMap R S)) :
    ∃ e : S, IsIdempotentElem e ∧ e - s ∈ I.map (algebraMap R S) := by
  cases subsingleton_or_nontrivial R with
  | inl _ =>
    have := Module.subsingleton R S
    exact ⟨s, Subsingleton.elim _ _, Subsingleton.elim (s - s) 0 ▸ zero_mem _⟩
  | inr _ =>
  -- `s * s - s` is integral over `I`: it is a root of a monic `q ≡ Xᵈ` modulo `I`.
  obtain ⟨q, hq, hqs, hqI⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hs
  set d := q.natDegree
  have hqmap : q.map (Ideal.Quotient.mk I) = X ^ d := by
    ext i
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy i d with hi | rfl | hi
    · rw [ite_eq_right hi.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hqI i)
    · rw [ite_eq_left rfl, ← leadingCoeff, hq.leadingCoeff, map_one]
    · rw [ite_eq_right hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero]
  -- So `s` is a root of the monic `P = q(X² - X) (X² - X) ≡ Xᵈ⁺¹ (X - 1)ᵈ⁺¹` modulo `I`.
  set Q : R[X] := X * (X - C 1)
  have hQ : Q.Monic := monic_X.mul (monic_X_sub_C 1)
  have hQdeg : Q.natDegree ≠ 0 := by
    rw [monic_X.natDegree_mul (monic_X_sub_C 1), natDegree_X]
    omega
  set P := q.comp Q * Q
  have hP : P.Monic := (hq.comp hQ hQdeg).mul hQ
  have hPs : aeval s P = 0 := by
    have : aeval s Q = s * s - s := by simp [Q]; ring
    rw [aeval_mul, aeval_comp, this, hqs, zero_mul]
  have hPmap : P.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - C 1) ^ (d + 1) := by
    have hQmap : Q.map (Ideal.Quotient.mk I) = X * (X - C 1) := by simp [Q]
    rw [Polynomial.map_mul, map_comp, hqmap, X_pow_comp, ← pow_succ, hQmap, mul_pow]
  have hcop : IsCoprime (X ^ (d + 1) : (R ⧸ I)[X]) ((X - C 1) ^ (d + 1)) :=
    IsCoprime.pow ⟨1, -1, by rw [map_one]; ring⟩
  obtain ⟨g, h, -, -, hgh, ⟨a, b, hab⟩, hgmap, hhmap⟩ :=
    exists_monic_mul_eq I hP (monic_X_pow _) ((monic_X_sub_C _).pow _) hcop hPmap
  refine ⟨aeval s (a * g), ?_, ?_⟩
  · -- `a(s) g(s)` and `b(s) h(s)` are complementary idempotents, since `g h = P` kills `s`.
    have h1 : aeval s (a * g) + aeval s (b * h) = 1 := by rw [← map_add, hab, map_one]
    have h0 : aeval s (a * g) * aeval s (b * h) = 0 := by
      rw [← map_mul, show a * g * (b * h) = a * b * P by rw [← hgh]; ring, map_mul, hPs,
        mul_zero]
    rw [IsIdempotentElem]
    linear_combination aeval s (a * g) * h1 - h0
  · -- Modulo `IS`, `g(s) ≡ sᵈ⁺¹ = s` and `h(s) s ≡ (s - 1)ᵈ⁺¹ s = 0`, so `a(s) g(s) ≡ s`.
    set J := I.map (algebraMap R S)
    set φ : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map
    set t := Ideal.Quotient.mk J s
    have hφ (f : R[X]) :
        Ideal.Quotient.mk J (aeval s f) = (f.map (Ideal.Quotient.mk I)).eval₂ φ t := by
      rw [aeval_def, hom_eval₂, eval₂_map, Ideal.quotientMap_comp_mk]
    have ht : IsIdempotentElem t := by
      rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq.mpr hs]
    have htt : (t - 1) ^ (d + 1) * t = 0 := by
      rw [pow_succ, mul_assoc, sub_mul, one_mul, ht.eq, sub_self, mul_zero]
    have hab' := congrArg (fun f : R[X] ↦ (f.map (Ideal.Quotient.mk I)).eval₂ φ t) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, hgmap, hhmap, eval₂_add, eval₂_mul,
      eval₂_pow, eval₂_sub, eval₂_X, map_one, Polynomial.map_one, eval₂_one] at hab'
    rw [← Ideal.Quotient.eq, hφ, Polynomial.map_mul, eval₂_mul, hgmap, eval₂_X_pow]
    linear_combination t * hab' - (eval₂ φ t (b.map (Ideal.Quotient.mk I))) * htt +
      (eval₂ φ t (a.map (Ideal.Quotient.mk I))) * (1 - t) * ht.pow_succ_eq d -
      (eval₂ φ t (a.map (Ideal.Quotient.mk I))) * ht.eq

/-- **Idempotents of an integral algebra over a Henselian pair.** If `(R, I)` is Henselian and `S`
is an integral `R`-algebra, the quotient map `S → S ⧸ IS` restricts to a bijection between the
idempotents of `S` and those of `S ⧸ IS`. -/
@[stacks 09XI "(1) ⇒ (3) and (4)"]
theorem bijOn_quotient_mk_map_isIdempotentElem :
    Set.BijOn (Ideal.Quotient.mk (I.map (algebraMap R S))) {e | IsIdempotentElem e}
      {t | IsIdempotentElem t} := by
  refine ⟨fun _ he ↦ he.map _, injOn_quotient_mk_map_isIdempotentElem I,
    fun t ht ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨e, he, hes⟩ := exists_isIdempotentElem_sub_mem_map_of_isIntegral I
    (Ideal.Quotient.eq.mp (show Ideal.Quotient.mk _ (s * s) = Ideal.Quotient.mk _ s by
      rw [map_mul]; exact ht.eq))
  exact ⟨e, he, Ideal.Quotient.eq.mpr hes⟩

end HenselianRing

section Converse

variable {R : Type*} [CommRing R]

/-- If `(x - c) e` lies in an ideal `K`, then so does `(p(x) - p(c)) e` for every polynomial `p`,
since `x - c` divides `p(x) - p(c)`. -/
private theorem aeval_sub_algebraMap_eval_mul_mem {S : Type*} [CommRing S] [Algebra R S]
    {K : Ideal S} {x e : S} {c : R} (he : (x - algebraMap R S c) * e ∈ K) (p : R[X]) :
    (aeval x p - algebraMap R S (p.eval c)) * e ∈ K := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub x (algebraMap R S c) (p.map (algebraMap R S))
  rw [eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply, coe_aeval_eq_eval] at hw
  rw [hw, mul_right_comm]
  exact K.mul_mem_right w he

/-- Let `e` be an idempotent of an `R`-algebra `S` that is projective as an `R`-module, with
`e S = R e`. Then the surjection `R → R e` splits: some `c : R` has `c e = e` and kills the
annihilator of `e`. -/
private theorem exists_smul_eq_self_and_mul_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    [Module.Projective R S] {e : S} (he : IsIdempotentElem e)
    (hσ : ∀ y : S, ∃ σ : R, σ • e = e * y) :
    ∃ c : R, c • e = e ∧ ∀ r : R, r • e = 0 → r * c = 0 := by
  -- The summand `e S` of `S` is projective, so `R → e S`, `r ↦ r e` has a section `τ`.
  let L := LinearMap.mulLeft R e
  have hL (y : S) : L y ∈ LinearMap.range L := LinearMap.mem_range_self L y
  have : Module.Projective R (LinearMap.range L) :=
    Module.Projective.of_split (LinearMap.range L).subtype (L.codRestrict _ hL) (by
      ext ⟨_, y, rfl⟩
      simp [L, ← mul_assoc, he.eq])
  let e' : LinearMap.range L := ⟨e, by simpa [L] using hL 1⟩
  have hρ : Function.Surjective (LinearMap.toSpanSingleton R (LinearMap.range L) e') := by
    rintro ⟨_, y, rfl⟩
    obtain ⟨σ, hσ⟩ := hσ y
    exact ⟨σ, Subtype.ext hσ⟩
  obtain ⟨τ, hτ⟩ := Module.projective_lifting_property _ LinearMap.id hρ
  refine ⟨τ e', congrArg Subtype.val (LinearMap.congr_fun hτ e'), fun r hr ↦ ?_⟩
  rw [← smul_eq_mul, ← map_smul, show r • e' = 0 from Subtype.ext hr, map_zero]

/-- Let `I` lie in the Jacobson radical of `R`, let `f` be monic and let `e` be an idempotent of
`R[X]/(f)` with `(X - a₀) e ≡ 0` modulo `I`, such that `r e ≡ 0` modulo `I` only for `r ∈ I`.
Then `f` has a root `a ≡ a₀` modulo `I`: Nakayama's lemma gives `e R[X]/(f) = R e`, so
`X e = a e`, and `R e` is free on `e`. -/
private theorem exists_isRoot_of_isIdempotentElem {I : Ideal R} (hjac : I ≤ Ideal.jacobson ⊥)
    {f : R[X]} (hf : f.Monic) {a₀ : R} {e : AdjoinRoot f} (he : IsIdempotentElem e)
    (hxe : (AdjoinRoot.root f - algebraMap R _ a₀) * e ∈ I.map (algebraMap R (AdjoinRoot f)))
    (hI : ∀ r : R, r • e ∈ I.map (algebraMap R (AdjoinRoot f)) → r ∈ I) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  have : Module.Free R (AdjoinRoot f) := hf.free_adjoinRoot
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  set x := AdjoinRoot.root f
  have hσ : ∀ y : AdjoinRoot f, ∃ σ : R, σ • e = e * y :=
    he.exists_smul_eq_mul_of_mul_sub_smul_mem hjac fun y ↦ by
      induction y using AdjoinRoot.induction_on with | ih p =>
      refine ⟨p.eval a₀, ?_⟩
      rw [← AdjoinRoot.aeval_eq, Algebra.smul_def, mul_comm e, ← sub_mul]
      exact aeval_sub_algebraMap_eval_mul_mem hxe p
  obtain ⟨a, ha⟩ := hσ x
  refine ⟨a, ?_, hI _ ?_⟩
  · -- `x e = a e` gives `f(a) e = f(x) e = 0`, and `r e = 0` forces `r c = 0` for a unit `c`.
    have hxa : (x - algebraMap R _ a) * e ∈ (⊥ : Ideal (AdjoinRoot f)) := by
      rw [Ideal.mem_bot, sub_mul, ← Algebra.smul_def, ha, mul_comm, sub_self]
    have hfa := aeval_sub_algebraMap_eval_mul_mem hxa f
    rw [Ideal.mem_bot, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_sub, neg_mul, neg_eq_zero,
      ← Algebra.smul_def] at hfa
    obtain ⟨c, hce, hc⟩ := exists_smul_eq_self_and_mul_eq_zero he hσ
    have hcu : IsUnit c := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hjac (hI _ (by
      rw [sub_smul, hce, one_smul, sub_self]; exact zero_mem _)))
    exact hcu.mul_left_eq_zero.mp (hc _ hfa)
  · convert hxe using 1
    rw [sub_smul, ha, Algebra.smul_def]
    ring

/-- **Henselian pairs from idempotents.** Let `I` be an ideal in the Jacobson radical of `R`. If for
every monic `f` over `R`, idempotents of `R[X]/(f)` modulo `I` lift to idempotents of `R[X]/(f)`,
then `(R, I)` is Henselian. -/
@[stacks 09XI "(3) ⇒ (1)"]
theorem henselianRing_of_forall_adjoinRoot {I : Ideal R} (hjac : I ≤ Ideal.jacobson ⊥)
    (H : ∀ f : R[X], f.Monic → ∀ s : AdjoinRoot f,
      s * s - s ∈ I.map (algebraMap R (AdjoinRoot f)) →
      ∃ e : AdjoinRoot f, IsIdempotentElem e ∧ e - s ∈ I.map (algebraMap R (AdjoinRoot f))) :
    HenselianRing R I where
  jac := hjac
  is_henselian f hf a₀ hfa₀ hunit := by
    set S := AdjoinRoot f
    set J := I.map (algebraMap R S)
    set x := AdjoinRoot.root f
    -- Evaluation at `a₀` modulo `I` kills `J`.
    let χ : S →ₐ[R] R ⧸ I :=
      AdjoinRoot.liftAlgHom f (Algebra.ofId R (R ⧸ I)) (Ideal.Quotient.mk I a₀) (by
        change aeval (algebraMap R (R ⧸ I) a₀) f = 0
        rw [aeval_algebraMap_apply, coe_aeval_eq_eval, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hfa₀)
    have hχJ : ∀ y ∈ J, χ y = 0 := by
      refine fun y hy ↦ (Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_ : J ≤ RingHom.ker χ) hy
      change χ (algebraMap R S r) = 0
      rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    -- Split off the root modulo `I`: `f = (X - a₀) q + f(a₀)` and `q(a₀) = f'(a₀)`.
    set q := f /ₘ (X - C a₀)
    have hfq : (X - C a₀) * q + C (f.eval a₀) = f := by
      rw [← modByMonic_X_sub_C_eq_C_eval, add_comm, modByMonic_add_div f (X - C a₀)]
    have hq : q.eval a₀ = f.derivative.eval a₀ := by
      conv_rhs => rw [← hfq]
      simp
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv'.mp hunit
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← hq, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hv
    -- `γ = u q(x)` is idempotent modulo `J`, with `(x - a₀) γ ∈ J` and `χ(γ) = 1`.
    have hxq : (x - algebraMap R S a₀) * aeval x q ∈ J := by
      have hfx : aeval x f = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := congrArg (aeval x) hfq
      rw [map_add, map_mul, map_sub, aeval_X, aeval_C, aeval_C, hfx] at this
      rw [eq_neg_of_add_eq_zero_left this]
      exact neg_mem (Ideal.mem_map_of_mem _ hfa₀)
    set γ := algebraMap R S u * aeval x q
    have hγ : γ * γ - γ ∈ J := by
      have h1 := aeval_sub_algebraMap_eval_mul_mem hxq q
      have h2 : algebraMap R S (u * q.eval a₀ - 1) ∈ J := Ideal.mem_map_of_mem _ hv
      have : γ * γ - γ = algebraMap R S u ^ 2 * ((aeval x q - algebraMap R S (q.eval a₀)) *
          aeval x q) + γ * algebraMap R S (u * q.eval a₀ - 1) := by
        simp only [γ, map_sub, map_mul, map_one]
        ring
      rw [this]
      exact add_mem (J.mul_mem_left _ h1) (J.mul_mem_left _ h2)
    have hχγ : χ γ = 1 := by
      rw [map_mul, AlgHom.commutes, ← aeval_algHom_apply, AdjoinRoot.liftAlgHom_root,
        show Ideal.Quotient.mk I a₀ = algebraMap R (R ⧸ I) a₀ from rfl, aeval_algebraMap_apply,
        coe_aeval_eq_eval, Ideal.Quotient.algebraMap_eq, ← map_mul,
        ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      exact hv
    -- Its idempotent lift `e` cuts out the factor `R[X]/(X - a₀)` of `R[X]/(f)`.
    obtain ⟨e, he, heγ⟩ := H f hf γ hγ
    refine exists_isRoot_of_isIdempotentElem hjac hf he ?_ fun r hr ↦ ?_
    · have : (x - algebraMap R S a₀) * e = (x - algebraMap R S a₀) * (e - γ) +
          algebraMap R S u * ((x - algebraMap R S a₀) * aeval x q) := by ring
      rw [this]
      exact add_mem (J.mul_mem_left _ heγ) (J.mul_mem_left _ hxq)
    · have hχe : χ e = 1 := by rw [← sub_add_cancel e γ, map_add, hχJ _ heγ, hχγ, zero_add]
      have := hχJ _ hr
      rwa [map_smul, hχe, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at this

end Converse

/-- **Henselian pairs and idempotents of finite algebras.** A pair `(R, I)` is Henselian if and
only if, for every finite `R`-algebra `S` in the universe of `R`, the quotient map `S → S ⧸ IS`
restricts to a bijection between the idempotents of `S` and those of `S ⧸ IS`. -/
@[stacks 09XI "(1) ⇔ (3)"]
theorem henselianRing_iff_forall_bijOn_isIdempotentElem {R : Type u} [CommRing R] {I : Ideal R} :
    HenselianRing R I ↔ ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      Set.BijOn (Ideal.Quotient.mk (I.map (algebraMap R S))) {e | IsIdempotentElem e}
        {t | IsIdempotentElem t} := by
  refine ⟨fun _ S _ _ _ ↦ HenselianRing.bijOn_quotient_mk_map_isIdempotentElem I,
    fun H ↦ henselianRing_of_forall_adjoinRoot ?_ fun f hf s hs ↦ ?_⟩
  · -- If `I ⊄ 𝔪` for a maximal ideal `𝔪`, then `0` and `1` in the field `R ⧸ 𝔪` both reduce to `0`.
    refine le_sInf fun m ⟨_, hm⟩ ↦ ?_
    by_contra hIm
    obtain ⟨i, hi, him⟩ := Set.not_subset.mp hIm
    have : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
    obtain ⟨b, c, hc, hbc⟩ := hm.exists_inv him
    have htop : I.map (algebraMap R (R ⧸ m)) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have : algebraMap R (R ⧸ m) (b * i) = 1 := by
        rw [← map_one (algebraMap R (R ⧸ m)), ← hbc, map_add, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.mpr hc, add_zero]
      exact this ▸ Ideal.mem_map_of_mem _ (I.mul_mem_left b hi)
    have := (H (R ⧸ m)).injOn (IsIdempotentElem.zero : IsIdempotentElem (0 : R ⧸ m))
      (IsIdempotentElem.one : IsIdempotentElem (1 : R ⧸ m))
      (Ideal.Quotient.eq.mpr (by rw [htop]; trivial))
    exact zero_ne_one this
  · have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
    obtain ⟨e, he, hes⟩ := (H (AdjoinRoot f)).surjOn
      (show IsIdempotentElem (Ideal.Quotient.mk _ s) by
        rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq.mpr hs])
    exact ⟨e, he, Ideal.Quotient.eq.mp hes⟩

namespace HenselianRing

/-- **Henselian pairs are stable under integral extensions.** If `(R, I)` is Henselian and `S` is
an integral `R`-algebra, then `(S, IS)` is Henselian. -/
@[stacks 09XK]
instance henselianRing_map_of_isIntegral {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    HenselianRing S (I.map (algebraMap R S)) :=
  henselianRing_of_forall_adjoinRoot (Ideal.map_le_jacobson_bot_of_isIntegral HenselianRing.jac)
    fun f hf s hs ↦ by
      have : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
      have : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.trans S
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hs ⊢
      exact exists_isIdempotentElem_sub_mem_map_of_isIntegral I hs

end HenselianRing

end TauCeti
