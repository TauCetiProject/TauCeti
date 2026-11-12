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

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)` its
Veronese subalgebra. A fraction of `A^{(d)}` of degree zero, `a / s` with `a, s` of degree `k` in
`A^{(d)}`, is a fraction of `A` of degree zero, with `a, s` of degree `d k` in `A`. This gives a
ring map from the homogeneous localization of `A^{(d)}` at a submonoid `P` to the homogeneous
localization of `A` at any submonoid `Q` containing the image of `P`.

For a homogeneous `f ∈ A^{(d)}` this map is an isomorphism

`A^{(d)}_{(f)} ≅ A_{(f)}`

(`TauCeti.GradedAlgebra.awayVeroneseEquiv`): if `f` has degree `k` in `A^{(d)}`, then an element
`a / fⁿ` of `A_{(f)}` has numerator `a ∈ 𝒜 (n d k) = 𝒜 (d (n k))`, which lies in `A^{(d)}`. These
isomorphisms are the affine charts of the identification `Proj A^{(d)} ≅ Proj A`, so they are
stated together with their compatibility with the transition maps `A_{(f)} → A_{(f g)}`, with the
degree-zero parts, and with graded ring maps.

## Main definitions

* `TauCeti.GradedAlgebra.veroneseLocalizationMap`: the map of localizations `A^{(d)}_P → A_Q`
  induced by the inclusion `A^{(d)} ⊆ A`.
* `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`: the map from the homogeneous
  localization of `A^{(d)}` at `P` to that of `A` at `Q`.
* `TauCeti.GradedAlgebra.awayVeroneseEquiv`: for homogeneous `f ∈ A^{(d)}`, the isomorphism
  `A^{(d)}_{(f)} ≃+* A_{(f)}`.

## Main results

* `TauCeti.GradedAlgebra.injective_veroneseHomogeneousLocalizationMap_powers` and
  `TauCeti.GradedAlgebra.surjective_veroneseHomogeneousLocalizationMap_powers`: the map
  `A^{(d)}_{(f)} → A_{(f)}` is bijective for homogeneous `f ∈ A^{(d)}`.
* `TauCeti.GradedAlgebra.awayVeroneseEquiv_awayMap`,
  `TauCeti.GradedAlgebra.awayVeroneseEquiv_fromZeroRingHom` and
  `TauCeti.GradedAlgebra.awayVeroneseEquiv_awayMap_veroneseMap`: these isomorphisms commute with
  the transition maps `A_{(f)} → A_{(f g)}`, with the maps from the degree-zero parts, and with
  the maps induced by a graded ring map.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

public section

open HomogeneousLocalization

namespace TauCeti.GradedAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ)
  {P : Submonoid (veronese 𝒜 d)} {Q : Submonoid A} (hPQ : P ≤ Q.comap (veronese 𝒜 d).val)

/-- The map of localizations `A^{(d)}_P → A_Q` induced by the inclusion of the Veronese
subalgebra `A^{(d)}` into `A`, for a submonoid `Q` of `A` containing the image of `P`. -/
noncomputable def veroneseLocalizationMap : Localization P →+* Localization Q :=
  IsLocalization.map _ (veronese 𝒜 d).val.toRingHom hPQ

@[simp]
theorem veroneseLocalizationMap_mk (a : veronese 𝒜 d) (s : P) :
    veroneseLocalizationMap 𝒜 d hPQ (.mk a s) = .mk (a : A) ⟨s, hPQ s.2⟩ := by
  simp only [veroneseLocalizationMap, Localization.mk_eq_mk']
  exact IsLocalization.map_mk' (T := Q) _ a s

@[simp]
theorem veroneseLocalizationMap_algebraMap (a : veronese 𝒜 d) :
    veroneseLocalizationMap 𝒜 d hPQ (algebraMap _ _ a) = algebraMap A _ (a : A) :=
  IsLocalization.map_eq _ a

variable {𝒜 d hPQ} in
/-- A fraction of degree `k` of the Veronese subalgebra, read as a fraction of degree `d k`
of `A`. -/
private def NumDenSameDeg.ofVeronese
    (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) : NumDenSameDeg 𝒜 Q where
  deg := d * c.deg
  num := ⟨(c.num : veronese 𝒜 d), c.num.2⟩
  den := ⟨(c.den : veronese 𝒜 d), c.den.2⟩
  den_mem := hPQ c.den_mem

private theorem embedding_ofVeronese (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) :
    (NumDenSameDeg.ofVeronese (hPQ := hPQ) c).embedding =
      veroneseLocalizationMap 𝒜 d hPQ c.embedding := by
  simp [NumDenSameDeg.embedding, NumDenSameDeg.ofVeronese]

/-- The function underlying `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`. -/
private def veroneseHomogeneousLocalizationFun :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P → HomogeneousLocalization 𝒜 Q :=
  Quotient.map' (NumDenSameDeg.ofVeronese (hPQ := hPQ)) fun x y (e : x.embedding = y.embedding) ↦
    (embedding_ofVeronese 𝒜 d hPQ x).trans <|
      (congrArg (veroneseLocalizationMap 𝒜 d hPQ) e).trans (embedding_ofVeronese 𝒜 d hPQ y).symm

private theorem val_veroneseHomogeneousLocalizationFun
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationFun 𝒜 d hPQ x).val =
      veroneseLocalizationMap 𝒜 d hPQ x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  exact embedding_ofVeronese 𝒜 d hPQ c

variable [NeZero d]

/-- The homogeneous localization of the Veronese subalgebra `A^{(d)}` at a submonoid `P` maps to
the homogeneous localization of `A` at a submonoid `Q` containing the image of `P`: a fraction of
degree `k` of `A^{(d)}` is a fraction of degree `d k` of `A`. -/
noncomputable def veroneseHomogeneousLocalizationMap :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P →+* HomogeneousLocalization 𝒜 Q where
  toFun := veroneseHomogeneousLocalizationFun 𝒜 d hPQ
  map_one' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_mul' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_zero' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_add' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]

/-- On underlying fractions, `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap` is
`TauCeti.GradedAlgebra.veroneseLocalizationMap`; this characterizes it, since
`HomogeneousLocalization.val` is injective. -/
@[simp]
theorem val_veroneseHomogeneousLocalizationMap
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationMap 𝒜 d hPQ x).val = veroneseLocalizationMap 𝒜 d hPQ x.val :=
  val_veroneseHomogeneousLocalizationFun 𝒜 d hPQ x

section Away

variable {𝒜 d} {f : veronese 𝒜 d}

omit [NeZero d] in
/-- The powers of `f ∈ A^{(d)}` map into the powers of `f` in `A`. -/
theorem powers_le_comap_val_powers :
    Submonoid.powers f ≤ (Submonoid.powers (f : A)).comap (veronese 𝒜 d).val :=
  Submonoid.map_le_iff_le_comap.1 (Submonoid.map_powers (veronese 𝒜 d).val f).le

/-- The map `A^{(d)}_{(f)} → A_{(f)}` is injective. -/
theorem injective_veroneseHomogeneousLocalizationMap_powers :
    Function.Injective
      (veroneseHomogeneousLocalizationMap 𝒜 d (powers_le_comap_val_powers (f := f))) := by
  intro x y e
  obtain ⟨c, rfl⟩ := x.mk_surjective
  obtain ⟨c', rfl⟩ := y.mk_surjective
  apply_fun HomogeneousLocalization.val at e
  simp only [val_veroneseHomogeneousLocalizationMap, val_mk, veroneseLocalizationMap_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := e
  refine val_injective _ ?_
  simp only [val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨⟨f ^ n, n, rfl⟩, Subtype.ext (by simpa using hn)⟩

/-- For homogeneous `f ∈ A^{(d)}`, the map `A^{(d)}_{(f)} → A_{(f)}` is surjective. -/
theorem surjective_veroneseHomogeneousLocalizationMap_powers {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) :
    Function.Surjective
      (veroneseHomogeneousLocalizationMap 𝒜 d (powers_le_comap_val_powers (f := f))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (mem_veroneseGrading.1 hf) z
  have ha' : a ∈ 𝒜 (d * (n • k)) := by
    rwa [smul_eq_mul, mul_left_comm, ← smul_eq_mul]
  refine ⟨Away.mk (veroneseGrading 𝒜 d) hf n ⟨a, mem_veronese_of_mem ha'⟩
    (mem_veroneseGrading.2 ha'), val_injective _ ?_⟩
  simp [Away.val_mk]

/-- For `f` homogeneous of degree `k` in the Veronese subalgebra `A^{(d)}`, the homogeneous
localizations `A^{(d)}_{(f)}` and `A_{(f)}` agree: a fraction `a / fⁿ` of `A` of degree zero has
numerator of degree `n d k`, so it is a fraction of `A^{(d)}`. -/
noncomputable def awayVeroneseEquiv {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k) :
    Away (veroneseGrading 𝒜 d) f ≃+* Away 𝒜 (f : A) :=
  .ofBijective _ ⟨injective_veroneseHomogeneousLocalizationMap_powers,
    surjective_veroneseHomogeneousLocalizationMap_powers hf⟩

@[simp]
theorem val_awayVeroneseEquiv {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k)
    (x : Away (veroneseGrading 𝒜 d) f) :
    (awayVeroneseEquiv hf x).val = veroneseLocalizationMap 𝒜 d powers_le_comap_val_powers x.val :=
  val_veroneseHomogeneousLocalizationMap 𝒜 d _ x

/-- `TauCeti.GradedAlgebra.awayVeroneseEquiv` sends the fraction `a / fⁿ` of `A^{(d)}` to the
same fraction of `A`. -/
@[simp]
theorem awayVeroneseEquiv_mk {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k) (n : ℕ)
    (a : veronese 𝒜 d) (ha : a ∈ veroneseGrading 𝒜 d (n • k)) :
    awayVeroneseEquiv hf (Away.mk _ hf n a ha) =
      Away.mk 𝒜 (mem_veroneseGrading.1 hf) n (a : A)
        (by simpa only [smul_eq_mul, mul_left_comm] using mem_veroneseGrading.1 ha) :=
  val_injective _ <| by simp [Away.val_mk]

/-- `TauCeti.GradedAlgebra.awayVeroneseEquiv` commutes with the transition maps
`A_{(f)} → A_{(f g)}`. -/
theorem awayVeroneseEquiv_awayMap {g x : veronese 𝒜 d} {k k' l : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hg : g ∈ veroneseGrading 𝒜 d k')
    (hx : x ∈ veroneseGrading 𝒜 d l) (hfg : x = f * g) (a : Away (veroneseGrading 𝒜 d) f) :
    awayVeroneseEquiv hx (awayMap _ hg hfg a) =
      awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hfg) (awayVeroneseEquiv hf a) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hf a
  subst hfg
  refine val_injective _ ?_
  rw [awayMap_mk, val_awayVeroneseEquiv, awayVeroneseEquiv_mk]
  simp [awayMap_mk, Away.val_mk]

/-- `TauCeti.GradedAlgebra.awayVeroneseEquiv` is compatible with the maps from the degree-zero
parts, which agree under `TauCeti.GradedAlgebra.veroneseGradingZeroEquiv`. -/
theorem awayVeroneseEquiv_fromZeroRingHom {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k)
    (a : veroneseGrading 𝒜 d 0) :
    awayVeroneseEquiv hf (fromZeroRingHom _ _ a) =
      fromZeroRingHom 𝒜 _ (veroneseGradingZeroEquiv 𝒜 d a) :=
  val_injective _ <| by
    rw [val_awayVeroneseEquiv, val_fromZeroRingHom, val_fromZeroRingHom,
      veroneseLocalizationMap_algebraMap, coe_veroneseGradingZeroEquiv]

variable {R' B : Type*} [CommRing R'] [CommRing B] [Algebra R' B] {ℬ : ℕ → Submodule R' B}
  [GradedAlgebra ℬ]

/-- `TauCeti.GradedAlgebra.awayVeroneseEquiv` commutes with the maps of homogeneous localizations
induced by a graded ring map `φ`. -/
theorem awayVeroneseEquiv_awayMap_veroneseMap (φ : 𝒜 →+*ᵍ ℬ) {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (a : Away (veroneseGrading 𝒜 d) f) :
    awayVeroneseEquiv ((veroneseMap d φ).map_mem hf) (Away.map (veroneseMap d φ) f a) =
      Away.map φ (f : A) (awayVeroneseEquiv hf a) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hf a
  rw [Away.map_mk, awayVeroneseEquiv_mk, awayVeroneseEquiv_mk, Away.map_mk]
  -- the two sides are the same fraction `φ a / φ fⁿ`, in the types `Away ℬ (veroneseMap d φ f)` and
  -- `Away ℬ (φ f)`, which agree definitionally (`coe_veroneseMap_apply` is `rfl`)
  rfl

end Away

end TauCeti.GradedAlgebra
