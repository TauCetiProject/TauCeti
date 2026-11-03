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

namespace Ideal

variable {R : Type u} [CommRing R] (K : ℕ → Ideal R) (hK : Antitone K)

/-- The inverse system of quotients by a decreasing sequence of ideals. -/
noncomputable abbrev quotientDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (R ⧸ K n.unop)
  map f := CommRingCat.ofHom (Ideal.Quotient.factor (hK (leOfHom f.unop)))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

end Ideal

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
    toQuotient I h = (evalₐ I n).toRingHom := by
  rw [toQuotient_eq I h le_rfl, Ideal.Quotient.factor_eq, RingHom.id_comp]

variable (K : ℕ → Ideal R) (hK : Antitone K)

variable (hopen : ∀ n, ∃ k : ℕ, I ^ k ≤ K n)

/-- The cone from the adic completion to a decreasing system of open ideal quotients. -/
noncomputable abbrev quotientCone : Cone (Ideal.quotientDiagram K hK) where
  pt := CommRingCat.of (AdicCompletion I R)
  π.app n := CommRingCat.ofHom (toQuotient I (hopen n.unop))
  π.naturality _ _ f := by
    ext x
    exact (factor_toQuotient I _ _ (hK (leOfHom f.unop)) x).symm

variable (hle : ∀ n, K n ≤ I ^ n)

/-- A decreasing quotient system between cofinal powers of `I` has the `I`-adic completion
as its limit in commutative rings. -/
noncomputable def isLimitQuotientCone : IsLimit (quotientCone I K hK hopen) := by
  -- First reduce a compatible cone to the usual power quotients and lift to the completion.
  let f (s : Cone (Ideal.quotientDiagram K hK)) (n : ℕ) : s.pt →+* R ⧸ I ^ n :=
    (Ideal.Quotient.factor (hle n)).comp (s.π.app (op n)).hom
  have hf (s : Cone (Ideal.quotientDiagram K hK)) {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow I hmn).comp (f s n) = f s m := by
    have hs := congrArg CommRingCat.Hom.hom (s.w (homOfLE hmn).op)
    simp only [CommRingCat.hom_comp, Ideal.quotientDiagram, CommRingCat.hom_ofHom] at hs
    ext x
    -- Expose the ring maps beneath the categorical cone and the local family `f`.
    change Ideal.Quotient.factorPow I hmn
      (Ideal.Quotient.factor (hle n) ((s.π.app (op n)).hom x)) =
        Ideal.Quotient.factor (hle m) ((s.π.app (op m)).hom x)
    have hx := congrArg (fun g : s.pt →+* R ⧸ K m ↦
      Ideal.Quotient.factor (hle m) (g x)) hs
    simpa only [Ideal.Quotient.factorPow, RingHom.comp_apply,
      Ideal.Quotient.factor_comp_apply] using hx
  refine
    { lift := fun s ↦ CommRingCat.ofHom (liftRingHom I (f s) (hf s))
      fac := ?_
      uniq := ?_ }
  · intro s n
    apply CommRingCat.hom_ext
    ext x
    -- The cone projection and the categorical lift are the displayed ring homomorphisms.
    change toQuotient I (hopen n.unop) (liftRingHom I (f s) (hf s) x) =
      (s.π.app n).hom x
    -- A common deeper level compares this lift with the original cone component.
    obtain ⟨k, hk⟩ := hopen n.unop
    let l := max k n.unop
    have hl : I ^ l ≤ K n.unop := (Ideal.pow_le_pow_right (le_max_left k n.unop)).trans hk
    rw [toQuotient_eq I (hopen n.unop) hl]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      evalₐ_liftRingHom]
    have hs := congrArg CommRingCat.Hom.hom
      (s.w (homOfLE (le_max_right k n.unop)).op)
    -- Normalize the categorical compatibility equation before evaluating it.
    change (Ideal.Quotient.factor (hK (le_max_right k n.unop))).comp
      (s.π.app (op l)).hom = (s.π.app n).hom at hs
    simpa only [f, RingHom.comp_apply, Ideal.Quotient.factor_comp_apply] using
      RingHom.congr_fun hs x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    -- Reduction from `K n` detects the `n`-th power component, hence detects equality.
    apply ext_evalₐ
    intro n
    -- Strip the bundled category morphisms to use the completion's evaluation API.
    change evalₐ I n (m.hom x) = evalₐ I n (liftRingHom I (f s) (hf s) x)
    have hproj := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hm (op n))) x
    change toQuotient I (hopen n) (m.hom x) = (s.π.app (op n)).hom x at hproj
    have hfactor := factor_toQuotient I (hopen n) ⟨n, le_rfl⟩ (hle n) (m.hom x)
    rw [toQuotient_pow] at hfactor
    simpa only [evalₐ_liftRingHom, f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, ← hproj] using hfactor.symm

end AdicCompletion
