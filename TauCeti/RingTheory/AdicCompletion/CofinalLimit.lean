/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Limit

/-!
# Cofinal quotient systems of an adic completion

The completion of a ring for an ideal `I` can be computed using a decreasing sequence `K n`
with `K n ≤ I ^ n`, provided each `K n` contains a power of `I`. This applies, for example,
to the sums of the separately extended powers of two ideals in a tensor product.

We first construct the projection of the completion onto any quotient by an ideal containing
a power of `I`. These projections form a limit cone for such a sequence `K`. Neither finite
generation nor completeness of the original ring is required.

Reference: Grothendieck–Dieudonné, EGA I, Ch. 0, §7.2 and 7.7.1.
-/

public section

open CategoryTheory Limits Opposite

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Projection of the `I`-adic completion onto a quotient by an ideal containing a power of `I`.
The map does not depend on the power used to construct it. -/
noncomputable def toQuotient {K : Ideal R} (hK : ∃ n : ℕ, I ^ n ≤ K) :
    AdicCompletion I R →+* R ⧸ K :=
  (Ideal.Quotient.factor hK.choose_spec).comp (evalₐ I hK.choose).toRingHom

/-- The projection to an open ideal quotient can be computed at any sufficiently deep level. -/
theorem toQuotient_eq {K : Ideal R} (hK : ∃ n : ℕ, I ^ n ≤ K) {n : ℕ} (hn : I ^ n ≤ K) :
    toQuotient I hK = (Ideal.Quotient.factor hn).comp (evalₐ I n).toRingHom := by
  ext x
  have h₁ := factor_evalₐ (I := I) (le_max_left hK.choose n) x
  have h₂ := factor_evalₐ (I := I) (le_max_right hK.choose n) x
  unfold toQuotient
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [← h₁, ← h₂, Ideal.Quotient.factor_comp_apply, Ideal.Quotient.factor_comp_apply]

/-- On elements of the original ring, projection to a quotient is the quotient map. -/
@[simp]
theorem toQuotient_of {K : Ideal R} (hK : ∃ n : ℕ, I ^ n ≤ K) (r : R) :
    toQuotient I hK (of I R r) = Ideal.Quotient.mk K r := by
  simp [toQuotient]

/-- Projection onto open ideal quotients commutes with reduction. -/
@[simp]
theorem factor_toQuotient {K L : Ideal R} (hK : ∃ n : ℕ, I ^ n ≤ K)
    (hL : ∃ n : ℕ, I ^ n ≤ L) (hKL : K ≤ L) (x : AdicCompletion I R) :
    Ideal.Quotient.factor hKL (toQuotient I hK x) = toQuotient I hL x := by
  rw [toQuotient_eq I hK hK.choose_spec,
    toQuotient_eq I hL (hK.choose_spec.trans hKL)]
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_comp_apply]

/-- The projection onto a power quotient is the usual evaluation map. -/
@[simp]
theorem toQuotient_pow (n : ℕ) (h : ∃ k : ℕ, I ^ k ≤ I ^ n) :
    toQuotient I h = (evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n) := by
  simp [toQuotient_eq I h le_rfl]

variable (K : ℕ → Ideal R) (hK : Antitone K)

variable (hopen : ∀ n, ∃ k : ℕ, I ^ k ≤ K n)

/-- The cone from the adic completion to a decreasing system of open ideal quotients. -/
noncomputable abbrev quotientCone : Cone (TauCeti.antitoneQuotientDiagram K hK) where
  pt := CommRingCat.of (AdicCompletion I R)
  π.app n := CommRingCat.ofHom (toQuotient I (hopen n.unop))
  π.naturality _ _ f := by
    ext x
    exact (factor_toQuotient I _ _ (hK (leOfHom f.unop)) x).symm

variable (hle : ∀ n, K n ≤ I ^ n)

/-- A compatible family of maps to ideal quotients finer than the power quotients induces
a map to the adic completion. The source may lie in any universe. -/
noncomputable def liftQuotientRingHom {D : Type*} [NonAssocSemiring D]
    (f : ∀ n, D →+* R ⧸ K n)
    (hf : ∀ {m n} (h : m ≤ n), (Ideal.Quotient.factor (hK h)).comp (f n) = f m) :
    D →+* AdicCompletion I R :=
  liftRingHom I (fun n ↦ (Ideal.Quotient.factor (hle n)).comp (f n)) (by
    intro m n h
    ext x
    have hx := congrArg (fun g : D →+* R ⧸ K m ↦ Ideal.Quotient.factor (hle m) (g x))
      (hf h)
    simpa only [Ideal.Quotient.factorPow, RingHom.comp_apply,
      Ideal.Quotient.factor_comp_apply] using hx)

/-- The induced map recovers each member of the compatible family under projection. -/
@[simp]
theorem toQuotient_comp_liftQuotientRingHom {D : Type*} [NonAssocSemiring D]
    (f : ∀ n, D →+* R ⧸ K n)
    (hf : ∀ {m n} (h : m ≤ n), (Ideal.Quotient.factor (hK h)).comp (f n) = f m)
    (n : ℕ) :
    (toQuotient I (hopen n)).comp (liftQuotientRingHom I K hK hle f hf) = f n := by
  ext x
  obtain ⟨k, hk⟩ := hopen n
  have hl : I ^ max k n ≤ K n := (Ideal.pow_le_pow_right (le_max_left k n)).trans hk
  rw [RingHom.comp_apply, toQuotient_eq I (hopen n) hl]
  dsimp only [liftQuotientRingHom]
  -- Abstract the compatibility proof so rewriting does not try to synthesize it again.
  generalize_proofs
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [evalₐ_liftRingHom I _ (by assumption)]
  simpa only [RingHom.comp_apply, Ideal.Quotient.factor_comp_apply] using
      RingHom.congr_fun (hf (le_max_right k n)) x

include hle in
/-- Maps to an adic completion are determined by their projections to a cofinal quotient
system. -/
theorem toQuotient_ext {D : Type*} [NonAssocSemiring D]
    {f g : D →+* AdicCompletion I R}
    (h : ∀ n, (toQuotient I (hopen n)).comp f = (toQuotient I (hopen n)).comp g) :
    f = g := by
  apply RingHom.ext
  intro x
  apply ext_evalₐ
  intro n
  have hx := congrArg (fun z ↦ Ideal.Quotient.factor (hle n) z) (RingHom.congr_fun (h n) x)
  simpa only [RingHom.comp_apply,
    factor_toQuotient I (hopen n) ⟨n, le_rfl⟩ (hle n), toQuotient_pow,
    AlgHom.coe_toRingHom] using hx

/-- A decreasing quotient system between cofinal powers of `I` has the `I`-adic completion
as its limit in commutative rings. -/
noncomputable def isLimitQuotientCone : IsLimit (quotientCone I K hK hopen) := by
  let hf (s : Cone (TauCeti.antitoneQuotientDiagram K hK)) {m n : ℕ} (h : m ≤ n) :=
    congrArg CommRingCat.Hom.hom (s.w (homOfLE h).op)
  refine
    { lift := fun s ↦ CommRingCat.ofHom
        (liftQuotientRingHom I K hK hle (fun n ↦ (s.π.app (op n)).hom) (hf s))
      fac := fun s n ↦ CommRingCat.hom_ext
        (toQuotient_comp_liftQuotientRingHom I K hK hopen hle _ (hf s) n.unop)
      uniq := ?_ }
  intro s m hm
  apply CommRingCat.hom_ext
  apply toQuotient_ext I K hopen hle
  intro n
  exact (congrArg CommRingCat.Hom.hom (hm (op n))).trans
    (toQuotient_comp_liftQuotientRingHom I K hK hopen hle _ (hf s) n).symm

end AdicCompletion
