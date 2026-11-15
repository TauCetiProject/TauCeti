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
a power of `I`. These projections form a limit cone for such a sequence `K`, and when a power of
`I` lies in `J` they assemble into an `R`-algebra homomorphism `AdicCompletion I R →ₐ[R]
AdicCompletion J R` (`AdicCompletion.ofPowLe`), giving an isomorphism `AdicCompletion.equivOfPowLe`
whenever `I` and `J` have mutually cofinal powers (for instance when they share a finitely
generated radical). Neither finite generation nor completeness of the original ring is required.

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

section PowLe

variable {I}

private theorem exists_pow_le_pow {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) (n : ℕ) :
    ∃ m : ℕ, I ^ m ≤ J ^ n :=
  let ⟨k, hk⟩ := hIJ
  ⟨k * n, (pow_mul I k n).le.trans (Ideal.pow_right_mono hk n)⟩

private theorem ofPowLe_aux {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (toQuotient I (exists_pow_le_pow hIJ n)) =
      toQuotient I (exists_pow_le_pow hIJ m) :=
  RingHom.ext fun x ↦ factor_toQuotient I _ _ (Ideal.pow_le_pow_right hmn) x

/-- When a power of `I` is contained in `J`, the projections onto `R ⧸ J ^ n` assemble into an
`R`-algebra homomorphism `AdicCompletion I R →ₐ[R] AdicCompletion J R`. The resulting map does not
depend on the chosen exponent. -/
noncomputable def ofPowLe {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) :
    AdicCompletion I R →ₐ[R] AdicCompletion J R :=
  let f := liftRingHom J (fun n ↦ toQuotient I (exists_pow_le_pow hIJ n)) (ofPowLe_aux hIJ)
  { f with
    toFun := f
    commutes' := fun r ↦ ext_evalₐ fun n ↦ by
      simpa only [f, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, toQuotient_of,
        evalₐ_of] using
        evalₐ_liftRingHom J (fun m ↦ toQuotient I (exists_pow_le_pow hIJ m)) (ofPowLe_aux hIJ) n
          (of I R r) }

/-- Evaluating `ofPowLe hIJ` modulo `J ^ n` recovers `toQuotient`. -/
@[simp]
theorem evalₐ_ofPowLe {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) (n : ℕ)
    (x : AdicCompletion I R) :
    evalₐ J n (ofPowLe hIJ x) =
      toQuotient I ⟨hIJ.choose * n,
        (pow_mul I hIJ.choose n).le.trans (Ideal.pow_right_mono hIJ.choose_spec n)⟩ x :=
  evalₐ_liftRingHom J (fun m ↦ toQuotient I (exists_pow_le_pow hIJ m)) (ofPowLe_aux hIJ) n x

/-- Projecting `ofPowLe hIJ` onto any open ideal quotient for `J` recovers `toQuotient` for `I`. -/
@[simp]
theorem toQuotient_ofPowLe {J L : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (hJL : ∃ n : ℕ, J ^ n ≤ L) (x : AdicCompletion I R) :
    toQuotient J hJL (ofPowLe hIJ x) =
      toQuotient I ⟨hIJ.choose * hJL.choose, (pow_mul I hIJ.choose hJL.choose).le.trans
        ((Ideal.pow_right_mono hIJ.choose_spec hJL.choose).trans hJL.choose_spec)⟩ x := by
  rw [toQuotient, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    evalₐ_ofPowLe hIJ hJL.choose, factor_toQuotient I _ _ hJL.choose_spec]

/-- `ofPowLe` commutes with the canonical maps from `R` into the completions. -/
@[simp]
theorem ofPowLe_of {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) (r : R) :
    ofPowLe hIJ (of I R r) = of J R r :=
  ext_evalₐ fun n ↦ by
    rw [evalₐ_ofPowLe hIJ n, toQuotient_of, evalₐ_of]

/-- `ofPowLe` is independent of the proof that a power of `I` lies in `J`, and composes
functorially across chains of ideals. -/
theorem ofPowLe_comp {J L : Ideal R} (hJL : ∃ k : ℕ, J ^ k ≤ L) (hIJ : ∃ k : ℕ, I ^ k ≤ J) :
    (ofPowLe hJL).comp (ofPowLe hIJ) =
      ofPowLe ⟨hIJ.choose * hJL.choose, (pow_mul I hIJ.choose hJL.choose).le.trans
        ((Ideal.pow_right_mono hIJ.choose_spec hJL.choose).trans hJL.choose_spec)⟩ :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    rw [AlgHom.comp_apply, evalₐ_ofPowLe hJL n, toQuotient_ofPowLe hIJ _, evalₐ_ofPowLe _ n]

/-- Pointwise form of `AdicCompletion.ofPowLe_comp`. -/
@[simp]
theorem ofPowLe_ofPowLe {J L : Ideal R} (hJL : ∃ k : ℕ, J ^ k ≤ L) (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (x : AdicCompletion I R) :
    ofPowLe hJL (ofPowLe hIJ x) =
      ofPowLe ⟨hIJ.choose * hJL.choose, (pow_mul I hIJ.choose hJL.choose).le.trans
        ((Ideal.pow_right_mono hIJ.choose_spec hJL.choose).trans hJL.choose_spec)⟩ x :=
  DFunLike.congr_fun (ofPowLe_comp hJL hIJ) x

/-- On a single ideal, `ofPowLe` is the identity algebra homomorphism. -/
@[simp]
theorem ofPowLe_id (hII : ∃ k : ℕ, I ^ k ≤ I) :
    ofPowLe hII = AlgHom.id R (AdicCompletion I R) :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    rw [evalₐ_ofPowLe hII n, toQuotient_pow, RingHom.coe_coe, AlgHom.id_apply]

/-- When `I ≤ J`, `ofPowLe` agrees with the functorial map `mapₐ (AlgHom.id A R)` for any scalar
ring `A`. -/
theorem ofPowLe_eq_mapₐ_id {A : Type*} [CommRing A] [Algebra A R] {J : Ideal R}
    (hIJ : ∃ k : ℕ, I ^ k ≤ J) (hle : I ≤ J.comap (AlgHom.id A R)) :
    (ofPowLe hIJ).restrictScalars A = mapₐ (AlgHom.id A R) hle :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    have hpow : I ^ n ≤ J ^ n :=
      Ideal.pow_right_mono (fun _ hr ↦ Ideal.mem_comap.mp (hle hr)) n
    rw [AlgHom.restrictScalars_apply, evalₐ_ofPowLe hIJ n, toQuotient_eq I _ hpow, evalₐ_mapₐ]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    simp [← hr]

/-- Two ideals with mutually cofinal powers have canonically isomorphic adic completions. -/
noncomputable def equivOfPowLe {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J R :=
  AlgEquiv.ofAlgHom (ofPowLe hIJ) (ofPowLe hJI)
    ((ofPowLe_comp hIJ hJI).trans (ofPowLe_id _))
    ((ofPowLe_comp hJI hIJ).trans (ofPowLe_id _))

/-- As an algebra homomorphism, `equivOfPowLe` is `ofPowLe`. -/
@[simp]
theorem toAlgHom_equivOfPowLe {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    (equivOfPowLe hIJ hJI : AdicCompletion I R →ₐ[R] AdicCompletion J R) = ofPowLe hIJ := by
  rw [equivOfPowLe]; exact AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- Applying `equivOfPowLe` agrees with `ofPowLe`. -/
@[simp]
theorem equivOfPowLe_apply {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) (x : AdicCompletion I R) :
    equivOfPowLe hIJ hJI x = ofPowLe hIJ x := by
  rw [equivOfPowLe, AlgEquiv.ofAlgHom_apply]

/-- On a single ideal, `equivOfPowLe` is the identity algebra isomorphism. -/
@[simp]
theorem equivOfPowLe_refl (h₁ h₂ : ∃ k : ℕ, I ^ k ≤ I) :
    equivOfPowLe h₁ h₂ = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective ((toAlgHom_equivOfPowLe h₁ h₂).trans (ofPowLe_id h₁))

/-- Swapping the ideal inclusions gives the inverse of `equivOfPowLe`. -/
@[simp]
theorem equivOfPowLe_symm {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    (equivOfPowLe hIJ hJI).symm = equivOfPowLe hJI hIJ := by
  ext x; simp [equivOfPowLe]

/-- Composing `equivOfPowLe` across a chain of three ideals gives `equivOfPowLe` for the composite
cofinality bounds. -/
@[simp]
theorem equivOfPowLe_trans {J L : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) (hJL : ∃ k : ℕ, J ^ k ≤ L) (hLJ : ∃ k : ℕ, L ^ k ≤ J) :
    (equivOfPowLe hIJ hJI).trans (equivOfPowLe hJL hLJ) =
      equivOfPowLe
        ⟨hIJ.choose * hJL.choose, (pow_mul I hIJ.choose hJL.choose).le.trans
          ((Ideal.pow_right_mono hIJ.choose_spec hJL.choose).trans hJL.choose_spec)⟩
        ⟨hLJ.choose * hJI.choose, (pow_mul L hLJ.choose hJI.choose).le.trans
          ((Ideal.pow_right_mono hLJ.choose_spec hJI.choose).trans hJI.choose_spec)⟩ := by
  ext x; simp

/-- `equivOfPowLe` commutes with the canonical maps from `R` into the completions. -/
theorem equivOfPowLe_of {J : Ideal R} (hIJ : ∃ k : ℕ, I ^ k ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) (r : R) :
    equivOfPowLe hIJ hJI (of I R r) = of J R r := by
  rw [equivOfPowLe_apply, ofPowLe_of]

/-- If `I ≤ J` and some power of `J` lies in `I`, the functorial map
`mapₐ (AlgHom.id A R) : AdicCompletion I R →ₐ[A] AdicCompletion J R` is bijective for any scalar
ring `A`. -/
theorem mapₐ_id_bijective_of_pow_le {A : Type*} [CommRing A] [Algebra A R] {J : Ideal R}
    (hle : I ≤ J.comap (AlgHom.id A R)) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    Function.Bijective (mapₐ (AlgHom.id A R) hle) := by
  have hIJ : ∃ k : ℕ, I ^ k ≤ J :=
    ⟨1, (pow_one I).le.trans fun _ hr ↦ Ideal.mem_comap.mp (hle hr)⟩
  have hcoe : ⇑(mapₐ (AlgHom.id A R) hle) = ⇑(equivOfPowLe hIJ hJI) := funext fun x ↦ by
    rw [← ofPowLe_eq_mapₐ_id hIJ hle, AlgHom.restrictScalars_apply, equivOfPowLe_apply]
  exact hcoe ▸ (equivOfPowLe hIJ hJI).bijective

end PowLe

end AdicCompletion
