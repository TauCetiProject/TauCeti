/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.GradedAlgebra.Veronese.Subalgebra

/-!
# Homogeneous localizations of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and
`A^{(d)} = ⨁ₖ 𝒜 (d k)` its Veronese subalgebra. Reinterpreting a fraction of degree `k` in
`A^{(d)}` as one of degree `d k` in `A` gives an `R`-algebra map on homogeneous localizations.
When the target denominator submonoid is the image of the source submonoid, this map is
bijective: a fraction `a / b` can be written as `a b^(d-1) / b^d`, whose degree is divisible by `d`.

In particular, for every `f ∈ A^{(d)}` there is an `R`-algebra isomorphism
`A^{(d)}_{(f)} ≅ A_{(f)}`. These isomorphisms provide the affine charts of the identification
`Proj A^{(d)} ≅ Proj A`. Both directions commute with chart transitions, the identification of
degree-zero parts, and maps induced by graded ring homomorphisms.

## Main definitions and results

* `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`: the map from the homogeneous
  localization of `A^{(d)}` at `P` to that of `A` at `Q`, where `Q` contains the image of `P`.
* `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap_injective` and
  `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap_surjective`: bijectivity when `Q`
  is the image of `P`.
* `TauCeti.GradedAlgebra.awayVeroneseEquiv`: the chart isomorphism
  `A^{(d)}_{(f)} ≃ₐ[R] A_{(f)}`, with fraction formulas in both directions.
* `TauCeti.GradedAlgebra.awayVeroneseEquiv_awayMap`,
  `TauCeti.GradedAlgebra.awayVeroneseEquiv_fromZeroRingHom`, and
  `TauCeti.GradedAlgebra.awayVeroneseEquiv_map_veroneseMap`: compatibility with chart transitions,
  degree-zero parts, and graded ring maps; each also has a `symm` counterpart.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

public section

open HomogeneousLocalization

namespace HomogeneousLocalization.NumDenSameDeg

open TauCeti.GradedAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {d : ℕ}
  {P : Submonoid (veronese 𝒜 d)} {Q : Submonoid A} {hPQ : P ≤ Q.comap (veronese 𝒜 d).val.toRingHom}

/-- A fraction of degree `k` of the Veronese subalgebra, read as a fraction of degree `d k`
of `A`. -/
private def ofVeronese
    (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) : NumDenSameDeg 𝒜 Q where
  deg := d * c.deg
  num := ⟨(c.num : veronese 𝒜 d), c.num.2⟩
  den := ⟨(c.den : veronese 𝒜 d), c.den.2⟩
  den_mem := hPQ c.den_mem

end HomogeneousLocalization.NumDenSameDeg

namespace TauCeti.GradedAlgebra

section Powers

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [SetLike.GradedMonoid 𝒜] {d : ℕ} {f : veronese 𝒜 d}

/-- The powers of a Veronese element map into its powers in the original algebra. -/
theorem powers_le_comap_val_powers :
    Submonoid.powers f ≤ (Submonoid.powers (f : A)).comap (veronese 𝒜 d).val.toRingHom :=
  Submonoid.map_le_iff_le_comap.mp (Submonoid.map_powers (veronese 𝒜 d).val f).le

end Powers

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ)
  {P : Submonoid (veronese 𝒜 d)} {Q : Submonoid A} (hPQ : P ≤ Q.comap (veronese 𝒜 d).val.toRingHom)

private theorem embedding_ofVeronese (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) :
    (NumDenSameDeg.ofVeronese (hPQ := hPQ) c).embedding =
      IsLocalization.map (Localization Q) (veronese 𝒜 d).val.toRingHom hPQ c.embedding := by
  simp [NumDenSameDeg.embedding, NumDenSameDeg.ofVeronese,
    Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The function underlying `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`. -/
private def veroneseHomogeneousLocalizationFun :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P → HomogeneousLocalization 𝒜 Q :=
  Quotient.map' (NumDenSameDeg.ofVeronese (hPQ := hPQ)) fun x y (e : x.embedding = y.embedding) ↦
    (embedding_ofVeronese 𝒜 d hPQ x).trans <|
      (congrArg (IsLocalization.map (Localization Q) (veronese 𝒜 d).val.toRingHom hPQ) e).trans
        (embedding_ofVeronese 𝒜 d hPQ y).symm

private theorem val_veroneseHomogeneousLocalizationFun
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationFun 𝒜 d hPQ x).val =
      IsLocalization.map (Localization Q) (veronese 𝒜 d).val.toRingHom hPQ x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  exact embedding_ofVeronese 𝒜 d hPQ c

variable [NeZero d]

/-- The homogeneous localization of the Veronese subalgebra `A^{(d)}` at a submonoid `P` maps to
the homogeneous localization of `A` at a submonoid `Q` containing the image of `P`: a fraction of
degree `k` of `A^{(d)}` is a fraction of degree `d k` of `A`. -/
noncomputable def veroneseHomogeneousLocalizationMap :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P →ₐ[R] HomogeneousLocalization 𝒜 Q where
  toFun := veroneseHomogeneousLocalizationFun 𝒜 d hPQ
  map_one' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_mul' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_zero' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_add' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  commutes' r := val_injective _ <| by
    rw [val_veroneseHomogeneousLocalizationFun, val_algebraMap, val_algebraMap,
      IsScalarTower.algebraMap_apply R (veronese 𝒜 d) (Localization P),
      IsLocalization.map_eq]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R A (Localization Q)]

/-- On underlying fractions, `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap` is
the ordinary localization map; this characterizes it, since
`HomogeneousLocalization.val` is injective. -/
@[simp]
theorem val_veroneseHomogeneousLocalizationMap
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationMap 𝒜 d hPQ x).val =
      IsLocalization.map (Localization Q) (veronese 𝒜 d).val.toRingHom hPQ x.val :=
  val_veroneseHomogeneousLocalizationFun 𝒜 d hPQ x

/-- Reinterpret a homogeneous fraction of the Veronese grading in the original grading. -/
@[simp]
theorem veroneseHomogeneousLocalizationMap_mk
    (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) :
    veroneseHomogeneousLocalizationMap 𝒜 d hPQ (mk c) =
      mk (𝒜 := 𝒜) (x := Q) ⟨d * c.deg, ⟨((c.num : veronese 𝒜 d) : A), c.num.2⟩,
        ⟨((c.den : veronese 𝒜 d) : A), c.den.2⟩, hPQ c.den_mem⟩ := by
  apply val_injective Q
  rw [val_veroneseHomogeneousLocalizationMap, val_mk, val_mk]
  exact (embedding_ofVeronese 𝒜 d hPQ c).symm

/-- The Veronese map respects the identification of degree-zero parts. -/
@[simp]
theorem veroneseHomogeneousLocalizationMap_fromZeroRingHom
    (a : veroneseGrading 𝒜 d 0) :
    veroneseHomogeneousLocalizationMap 𝒜 d hPQ (fromZeroRingHom _ P a) =
      fromZeroRingHom 𝒜 Q (veroneseGradingZeroEquiv 𝒜 d a) := by
  apply val_injective Q
  simp [coe_veroneseGradingZeroEquiv]

/-- The Veronese homogeneous localization map is injective when the denominator submonoid
is the image of the source denominator submonoid. -/
theorem veroneseHomogeneousLocalizationMap_injective
    (hQP : Q ≤ P.map (veronese 𝒜 d).val) :
    Function.Injective (veroneseHomogeneousLocalizationMap 𝒜 d hPQ) := by
  have hQ : Q = P.map (veronese 𝒜 d).val :=
    le_antisymm hQP (Submonoid.map_le_iff_le_comap.mpr hPQ)
  subst Q
  intro x y h
  apply val_injective P
  exact IsLocalization.map_injective_of_injective P (Localization P) _ Subtype.val_injective
    ((val_veroneseHomogeneousLocalizationMap ..).symm.trans
      ((congrArg val h).trans (val_veroneseHomogeneousLocalizationMap ..)))

/-- The Veronese homogeneous localization map is surjective when every target denominator
comes from the source submonoid: replace `a / b` by `a b^(d-1) / b^d`. -/
theorem veroneseHomogeneousLocalizationMap_surjective
    (hQP : Q ≤ P.map (veronese 𝒜 d).val) :
    Function.Surjective (veroneseHomogeneousLocalizationMap 𝒜 d hPQ) := by
  intro z
  obtain ⟨c, rfl⟩ := z.mk_surjective
  obtain ⟨b, hb, he⟩ := hQP c.den_mem
  simp only [Subalgebra.val_apply] at he
  have hdeg : c.deg + (d - 1) • c.deg = d * c.deg := by
    rw [smul_eq_mul, add_comm, ← Nat.succ_mul, Nat.succ_eq_add_one,
      Nat.sub_one_add_one (NeZero.ne d)]
  have hn : (c.num : A) * (c.den : A) ^ (d - 1) ∈ 𝒜 (d * c.deg) :=
    hdeg ▸ SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded (d - 1) c.den.2)
  have hd : (b ^ d : veronese 𝒜 d) ∈ veroneseGrading 𝒜 d c.deg := by
    simpa [mem_veroneseGrading, he, smul_eq_mul] using SetLike.pow_mem_graded d c.den.2
  refine ⟨mk ⟨c.deg, ⟨⟨_, mem_veronese_of_mem hn⟩, hn⟩, ⟨b ^ d, hd⟩, P.pow_mem hb d⟩,
    val_injective Q ?_⟩
  simp only [veroneseHomogeneousLocalizationMap_mk, val_mk,
    Localization.mk_eq_mk', Subalgebra.coe_pow, he]
  convert IsLocalization.mk'_cancel (S := Localization Q) (c.num : A)
    ⟨c.den, c.den_mem⟩ (⟨c.den, c.den_mem⟩ ^ (d - 1)) using 1
  simp [← pow_succ', Nat.sub_one_add_one (NeZero.ne d)]

section Map

variable {R' B : Type*} [CommRing R'] [CommRing B] [Algebra R' B]
  (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ]
  {P' : Submonoid (veronese ℬ d)} {Q' : Submonoid B}

/-- Veronese comparison commutes with maps induced by a graded ring homomorphism. -/
theorem veroneseHomogeneousLocalizationMap_map (φ : 𝒜 →+*ᵍ ℬ)
    (hP'Q' : P' ≤ Q'.comap (veronese ℬ d).val.toRingHom)
    (hPP' : P ≤ P'.comap (veroneseMap d φ)) (hQQ' : Q ≤ Q'.comap φ)
    (a : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    veroneseHomogeneousLocalizationMap ℬ d hP'Q' (map (veroneseMap d φ) hPP' a) =
      map φ hQQ' (veroneseHomogeneousLocalizationMap 𝒜 d hPQ a) := by
  obtain ⟨c, rfl⟩ := a.mk_surjective
  rw [map_mk, veroneseHomogeneousLocalizationMap_mk,
    veroneseHomogeneousLocalizationMap_mk, map_mk]
  -- Both sides represent the same fraction; `coe_veroneseMap_apply` is definitionally equal
  -- to applying `φ`, as exposed by the Veronese subalgebra API.
  rfl

end Map

section Away

variable {𝒜 d} (f : veronese 𝒜 d)

/-- The homogeneous localizations `A^{(d)}_{(f)}` and `A_{(f)}` agree as `R`-algebras.
No homogeneity assumption on `f` is needed. -/
noncomputable def awayVeroneseEquiv :
    Away (veroneseGrading 𝒜 d) f ≃ₐ[R] Away 𝒜 (f : A) :=
  AlgEquiv.ofBijective
    (veroneseHomogeneousLocalizationMap 𝒜 d
      (powers_le_comap_val_powers (f := f)))
    ⟨veroneseHomogeneousLocalizationMap_injective 𝒜 d (powers_le_comap_val_powers (f := f))
        (Submonoid.map_powers (veronese 𝒜 d).val f).ge,
      veroneseHomogeneousLocalizationMap_surjective 𝒜 d (powers_le_comap_val_powers (f := f))
        (Submonoid.map_powers (veronese 𝒜 d).val f).ge⟩

/-- The algebra homomorphism underlying the Veronese chart equivalence. -/
theorem toAlgHom_awayVeroneseEquiv :
    (awayVeroneseEquiv f).toAlgHom = veroneseHomogeneousLocalizationMap 𝒜 d
      (powers_le_comap_val_powers (f := f)) := by
  ext x
  rfl

@[simp]
theorem val_awayVeroneseEquiv (x : Away (veroneseGrading 𝒜 d) f) :
    (awayVeroneseEquiv f x).val =
      IsLocalization.map (Localization.Away (f : A)) (veronese 𝒜 d).val.toRingHom
        (powers_le_comap_val_powers (f := f)) x.val :=
  val_veroneseHomogeneousLocalizationMap 𝒜 d _ x

variable {f}

/-- The chart equivalence sends a homogeneous fraction to the same fraction in `A`. -/
@[simp]
theorem awayVeroneseEquiv_mk {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k) (n : ℕ)
    (a : veronese 𝒜 d) (ha : a ∈ veroneseGrading 𝒜 d (n • k)) :
    awayVeroneseEquiv f (Away.mk _ hf n a ha) =
      Away.mk 𝒜 (mem_veroneseGrading.1 hf) n (a : A)
        (by simpa only [smul_eq_mul, mul_left_comm] using mem_veroneseGrading.1 ha) :=
  val_injective _ <| by simp [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The inverse chart equivalence regards the numerator of a homogeneous fraction as an
element of the Veronese subalgebra. -/
@[simp]
theorem awayVeroneseEquiv_symm_mk {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • (d * k))) :
    (awayVeroneseEquiv f).symm (Away.mk 𝒜 (mem_veroneseGrading.1 hf) n a ha) =
      Away.mk (veroneseGrading 𝒜 d) hf n
        ⟨a, mem_veronese_of_mem (k := n • k)
          (by simpa only [smul_eq_mul, mul_left_comm] using ha)⟩
        (by simpa only [mem_veroneseGrading, smul_eq_mul, mul_left_comm] using ha) := by
  apply (awayVeroneseEquiv f).injective
  rw [AlgEquiv.apply_symm_apply, awayVeroneseEquiv_mk]

/-- The Veronese chart equivalence commutes with the transition maps `A_{(f)} → A_{(fg)}`. -/
theorem awayVeroneseEquiv_awayMap {g x : veronese 𝒜 d} {k' : ℕ}
    (hg : g ∈ veroneseGrading 𝒜 d k') (hfg : x = f * g)
    (a : Away (veroneseGrading 𝒜 d) f) :
    awayVeroneseEquiv x (awayMap _ hg hfg a) =
      awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hfg) (awayVeroneseEquiv f a) := by
  apply val_injective _
  rw [val_awayVeroneseEquiv, val_awayMap, val_awayMap, val_awayVeroneseEquiv,
    ← RingHom.comp_apply, ← RingHom.comp_apply]
  congr 1
  apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
  ext b
  simp [Localization.awayLift]

/-- The inverse Veronese chart equivalence commutes with chart transitions. -/
theorem awayVeroneseEquiv_symm_awayMap {g x : veronese 𝒜 d} {k' : ℕ}
    (hg : g ∈ veroneseGrading 𝒜 d k') (hfg : x = f * g) (a : Away 𝒜 (f : A)) :
    (awayVeroneseEquiv x).symm
        (awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hfg) a) =
      awayMap _ hg hfg ((awayVeroneseEquiv f).symm a) := by
  apply (awayVeroneseEquiv x).injective
  simp only [AlgEquiv.apply_symm_apply, awayVeroneseEquiv_awayMap]

/-- The chart equivalence respects the identification of the degree-zero parts. -/
@[simp]
theorem awayVeroneseEquiv_fromZeroRingHom (a : veroneseGrading 𝒜 d 0) :
    awayVeroneseEquiv f (fromZeroRingHom _ _ a) =
      fromZeroRingHom 𝒜 _ (veroneseGradingZeroEquiv 𝒜 d a) :=
  veroneseHomogeneousLocalizationMap_fromZeroRingHom 𝒜 d _ a

/-- The inverse chart equivalence respects the identification of the degree-zero parts. -/
@[simp]
theorem awayVeroneseEquiv_symm_fromZeroRingHom (a : 𝒜 0) :
    (awayVeroneseEquiv f).symm (fromZeroRingHom 𝒜 _ a) =
      fromZeroRingHom _ _ ((veroneseGradingZeroEquiv 𝒜 d).symm a) := by
  apply (awayVeroneseEquiv f).injective
  simp

variable {R' B : Type*} [CommRing R'] [CommRing B] [Algebra R' B]
  {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ]

/-- The chart equivalence commutes with the maps induced by a graded ring homomorphism. -/
theorem awayVeroneseEquiv_map_veroneseMap (φ : 𝒜 →+*ᵍ ℬ)
    (a : Away (veroneseGrading 𝒜 d) f) :
    awayVeroneseEquiv (veroneseMap d φ f) (Away.map (veroneseMap d φ) f a) =
      Away.map φ (f : A) (awayVeroneseEquiv f a) :=
  veroneseHomogeneousLocalizationMap_map 𝒜 d _ ℬ φ _ _ _ a

/-- The inverse chart equivalence commutes with maps induced by a graded ring homomorphism. -/
theorem awayVeroneseEquiv_symm_map_veroneseMap (φ : 𝒜 →+*ᵍ ℬ) (a : Away 𝒜 (f : A)) :
    (awayVeroneseEquiv (veroneseMap d φ f)).symm (Away.map φ (f : A) a) =
      Away.map (veroneseMap d φ) f ((awayVeroneseEquiv f).symm a) := by
  apply (awayVeroneseEquiv (veroneseMap d φ f)).injective
  rw [awayVeroneseEquiv_map_veroneseMap, AlgEquiv.apply_symm_apply]
  exact (awayVeroneseEquiv (veroneseMap d φ f)).apply_symm_apply _

end Away

end TauCeti.GradedAlgebra
