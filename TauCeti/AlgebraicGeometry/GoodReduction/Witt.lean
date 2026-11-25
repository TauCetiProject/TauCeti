/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Domain
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
public import TauCeti.RingTheory.WittVector.PadicInt

/-!
# Good reduction over the unramified Witt ring

Let `X` be a scheme over `Spec ℚ` and `p` a prime. Write `W` for the ring of Witt vectors of an
algebraic closure of `𝔽ₚ`, the complete unramified discrete valuation ring with algebraically
closed residue field of characteristic `p`, and `K = Frac W` for its fraction field. We say that
`X` has *Witt good reduction at `p`* if, after extending scalars along the (unique) ring map
`ℚ → K`, it becomes isomorphic over `K` to the generic fibre of a smooth proper `W`-scheme. It
has *everywhere Witt good reduction* if this holds at every prime, including `2`. The models at
different primes are independent witnesses: no common model, polarization or compatibility
between primes is part of the definition.

This is the local hypothesis of Fontaine's theorem that a smooth proper `ℚ`-scheme with good
reduction at every prime has `Hʲ(X, Ωⁱ) = 0` for `i ≠ j` and `i + j ≤ 3`. Working over `W` rather
than over `ℤₚ` asks for a model only after the maximal unramified extension, completed; a smooth
proper model over `ℤₚ`, or over `ℤ`, gives such a model by base change. A model which only
exists after a ramified extension of `ℚₚ` does not qualify.

## Main definitions

* `TauCeti.AlgebraicGeometry.HasWittGoodReductionAt f p`: the scalar extension of
  `f : X ⟶ Spec ℚ` to `Frac W` is the generic fibre of a smooth proper `W`-scheme.
* `TauCeti.AlgebraicGeometry.HasEverywhereWittGoodReduction f`: Witt good reduction at every
  prime.

## Main results

* `TauCeti.AlgebraicGeometry.HasEverywhereWittGoodReduction.hasWittGoodReductionAt`: everywhere
  Witt good reduction gives Witt good reduction at each prime.
* `TauCeti.AlgebraicGeometry.hasWittGoodReductionAt_iff`: the definition, for a given ring map
  `ℚ → Frac W`; any two such maps agree.
* `TauCeti.AlgebraicGeometry.hasWittGoodReductionAt_iff_exists_isPullback`: Witt good reduction
  means that one scheme over `Frac W` is the base change both of `X` and of a smooth proper
  `W`-scheme.
* `TauCeti.AlgebraicGeometry.hasWittGoodReductionAt_iff_exists_model`: Witt good reduction
  means that `X ×_ℚ Frac W` has a smooth proper model over `W`, as a `TauCeti.Model`.
* `TauCeti.AlgebraicGeometry.HasWittGoodReductionAt.of_isPullback`: a smooth proper model over
  a ring `R` whose base change to a ring `L` is `X ×_ℚ L` gives Witt good reduction, as soon as
  `R → L` maps compatibly to `W → Frac W`.
* `TauCeti.AlgebraicGeometry.HasWittGoodReductionAt.of_padicInt`: a smooth proper `ℤₚ`-scheme
  whose generic fibre is `X ×_ℚ ℚₚ` gives Witt good reduction at `p`.
* `TauCeti.AlgebraicGeometry.HasEverywhereWittGoodReduction.of_int`: the generic fibre of a smooth
  proper `ℤ`-scheme has everywhere Witt good reduction.
* `TauCeti.AlgebraicGeometry.hasWittGoodReductionAt_iff_of_iso`,
  `TauCeti.AlgebraicGeometry.hasEverywhereWittGoodReduction_iff_of_iso`: both properties are
  invariant under isomorphism of schemes over `ℚ`.
* `TauCeti.AlgebraicGeometry.hasEverywhereWittGoodReduction_id`: `Spec ℚ` has everywhere Witt
  good reduction.

## References

* J.-M. Fontaine, *Schémas propres et lisses sur Z*, Proceedings of the Indo-French Conference on
  Geometry (Bombay, 1989), Hindustan Book Agency (1993), 43–56; Theorem 1 and Remark (a).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

variable {X X' : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) (p : ℕ) [Fact p.Prime]

/-- **Witt good reduction at `p`.** A scheme `f : X ⟶ Spec ℚ` has Witt good reduction at the
prime `p` if, for some (equivalently, the unique) ring map `a : ℚ → K` to the fraction field `K`
of the ring `W` of Witt vectors of an algebraic closure of `𝔽ₚ`, there is a smooth proper
scheme `g : Y ⟶ Spec W` and an isomorphism of `K`-schemes between the scalar extension
`X ×_ℚ K` and the generic fibre `Y ×_W K`. -/
def HasWittGoodReductionAt : Prop :=
  ∃ (a : ℚ →+* FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (Y : Scheme.{0})
    (g : Y ⟶ Spec (.of (WittVector p (AlgebraicClosure (ZMod p))))), Smooth g ∧ IsProper g ∧
    ∃ e : pullback f (Spec.map (CommRingCat.ofHom a)) ≅
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _

/-- **Everywhere Witt good reduction.** A scheme `f : X ⟶ Spec ℚ` has everywhere Witt good
reduction if it has Witt good reduction at every prime `p`, including `2`. The smooth proper
models at the different primes are independent of each other. -/
def HasEverywhereWittGoodReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], HasWittGoodReductionAt f p

variable {f p}

/-- Everywhere Witt good reduction is Witt good reduction at every prime. -/
theorem hasEverywhereWittGoodReduction_iff :
    HasEverywhereWittGoodReduction f ↔ ∀ (p : ℕ) [Fact p.Prime], HasWittGoodReductionAt f p :=
  Iff.rfl

/-- A scheme with everywhere Witt good reduction has Witt good reduction at each prime `q`. -/
theorem HasEverywhereWittGoodReduction.hasWittGoodReductionAt
    (hf : HasEverywhereWittGoodReduction f) (q : ℕ) [Fact q.Prime] :
    HasWittGoodReductionAt f q :=
  hf q

/-- Witt good reduction at `p`, for a given ring map `a : ℚ → Frac W`, where `W` is the ring of
Witt vectors of an algebraic closure of `𝔽ₚ`: such a map is unique, so the existential quantifier
over it in the definition may be replaced by any choice. -/
theorem hasWittGoodReductionAt_iff
    (a : ℚ →+* FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) :
    HasWittGoodReductionAt f p ↔
      ∃ (Y : Scheme.{0}) (g : Y ⟶ Spec (.of (WittVector p (AlgebraicClosure (ZMod p))))),
        Smooth g ∧ IsProper g ∧
        ∃ e : pullback f (Spec.map (CommRingCat.ofHom a)) ≅
            pullback g (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))),
          e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  refine ⟨fun ⟨a', h⟩ ↦ ?_, fun h ↦ ⟨a, h⟩⟩
  rwa [Subsingleton.elim a' a] at h

/-- **Witt good reduction through pullback squares.** For a ring map `a : ℚ → K`, where
`K = Frac W` and `W` is the ring of Witt vectors of an algebraic closure of `𝔽ₚ`, the scheme `X`
has Witt good reduction at `p` exactly when there are a smooth proper scheme `g : Y ⟶ Spec W` and
a scheme `s : X_K ⟶ Spec K` which is the base change of `X` along `Spec a` and of `Y` along
`Spec K ⟶ Spec W`. -/
theorem hasWittGoodReductionAt_iff_exists_isPullback
    (a : ℚ →+* FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) :
    HasWittGoodReductionAt f p ↔
      ∃ (Y : Scheme.{0}) (g : Y ⟶ Spec (.of (WittVector p (AlgebraicClosure (ZMod p))))),
        Smooth g ∧ IsProper g ∧
        ∃ (XK : Scheme.{0}) (h : XK ⟶ X) (φ : XK ⟶ Y)
          (s : XK ⟶ Spec (.of (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))))),
          IsPullback h s f (Spec.map (CommRingCat.ofHom a)) ∧
            IsPullback φ s g (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) := by
  rw [hasWittGoodReductionAt_iff a]
  constructor
  · rintro ⟨Y, g, hs, hp, e, he⟩
    refine ⟨Y, g, hs, hp, _, pullback.fst _ _, e.hom ≫ pullback.fst _ _, pullback.snd _ _,
      .of_hasPullback _ _, .of_iso_pullback ⟨?_⟩ e rfl he⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  · rintro ⟨Y, g, hs, hp, XK, h, φ, s, hX, hY⟩
    exact ⟨Y, g, hs, hp, hX.isoPullback.symm ≪≫ hY.isoPullback, by simp⟩

/-- **Witt good reduction through models.** For a ring map `a : ℚ → K`, where `K = Frac W` and
`W` is the ring of Witt vectors of an algebraic closure of `𝔽ₚ`, the scheme `X` has Witt good
reduction at `p` exactly when the scalar extension `X ×_ℚ K` has a smooth proper model over the
discrete valuation ring `W`, in the sense of `TauCeti.Model`. -/
theorem hasWittGoodReductionAt_iff_exists_model
    (a : ℚ →+* FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) :
    HasWittGoodReductionAt f p ↔
      ∃ M : Model (WittVector p (AlgebraicClosure (ZMod p)))
          (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
          (pullback f (Spec.map (CommRingCat.ofHom a))) (pullback.snd _ _),
        Smooth M.toBase ∧ M.IsProper := by
  rw [hasWittGoodReductionAt_iff a]
  constructor
  · rintro ⟨Y, g, hs, hp, e, he⟩
    exact ⟨⟨Y, g, inferInstance, inferInstance, inferInstance, inferInstance,
      Over.isoMk e.symm (by simp [← he])⟩, hs, hp⟩
  · rintro ⟨M, hs, hp⟩
    exact ⟨M.total, M.toBase, hs, hp, (Over.forget _).mapIso M.genericFiberIso.symm,
      by simpa using Over.w M.genericFiberIso.inv⟩

/-- **Models over a ring give Witt good reduction.** Let `R` be a ring with maps `i : R → L` to a
`ℚ`-algebra `L` (through `a : ℚ → L`) and `j : R → W`, where `W` is the ring of Witt vectors
of an algebraic closure of `𝔽ₚ`, and let `k : L → Frac W` be compatible with them. If
`g : Y ⟶ Spec R` is smooth and proper and the base change `X ×_ℚ L` is the generic fibre
`Y ×_R L`, then `X` has Witt good reduction at `p`: base change `Y` along `j`. -/
theorem HasWittGoodReductionAt.of_isPullback {R L : Type} [CommRing R] [CommRing L]
    (a : ℚ →+* L) (i : R →+* L) (j : R →+* WittVector p (AlgebraicClosure (ZMod p)))
    (k : L →+* FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
    (hk : k.comp i = (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))).comp j)
    {Y XL : Scheme.{0}} (g : Y ⟶ Spec (.of R)) [Smooth g] [IsProper g]
    (h : XL ⟶ X) (φ : XL ⟶ Y) (s : XL ⟶ Spec (.of L))
    (hX : IsPullback h s f (Spec.map (CommRingCat.ofHom a)))
    (hY : IsPullback φ s g (Spec.map (CommRingCat.ofHom i))) :
    HasWittGoodReductionAt f p := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
    (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))))
  set sk := Spec.map (CommRingCat.ofHom k)
  -- the square `Spec K ⟶ Spec L ⟶ Spec R` agrees with `Spec K ⟶ Spec W ⟶ Spec R`
  have hsk : sk ≫ Spec.map (CommRingCat.ofHom i) = b ≫ Spec.map (CommRingCat.ofHom j) := by
    simp only [sk, b, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hk]
  -- the base change of `X_L` to `K` is the base change of `X`, and of `Y`, to `K`
  have hXK := (IsPullback.of_hasPullback s sk).paste_horiz hX
  have hYK := (IsPullback.of_hasPullback s sk).paste_horiz hY
  rw [hsk] at hYK
  rw [hasWittGoodReductionAt_iff_exists_isPullback (k.comp a)]
  refine ⟨_, pullback.snd g (Spec.map (CommRingCat.ofHom j)), inferInstance, inferInstance, _,
    pullback.fst s sk ≫ h, pullback.lift (pullback.fst s sk ≫ φ) (pullback.snd s sk ≫ b)
      (by simpa using hYK.w), pullback.snd s sk, ?_, ?_⟩
  · rwa [CommRingCat.ofHom_comp, Spec.map_comp]
  · exact IsPullback.of_right (by simpa using hYK) (by simp [b]) (.of_hasPullback _ _)

/-- **A smooth proper `ℤₚ`-model gives Witt good reduction at `p`.** If `X ×_ℚ ℚₚ` is the generic
fibre of a smooth proper scheme `g : Y ⟶ Spec ℤₚ`, then `X` has Witt good reduction at `p`: the
base change of `Y` along `ℤₚ = W(𝔽ₚ) → W` is a model over the ring `W` of Witt vectors of an
algebraic closure of `𝔽ₚ`. -/
theorem HasWittGoodReductionAt.of_padicInt {Y XL : Scheme.{0}} (g : Y ⟶ Spec (.of ℤ_[p]))
    [Smooth g] [IsProper g] (h : XL ⟶ X) (φ : XL ⟶ Y) (s : XL ⟶ Spec (.of ℚ_[p]))
    (hX : IsPullback h s f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[p]))))
    (hY : IsPullback φ s g (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p])))) :
    HasWittGoodReductionAt f p := by
  -- `ℤₚ → W` is injective, so it extends to the fraction fields
  have hj : Function.Injective ((algebraMap _
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))).comp
        (TauCeti.WittVector.padicIntHom p (AlgebraicClosure (ZMod p)))) :=
    (IsFractionRing.injective _ _).comp
      (TauCeti.WittVector.padicIntHom_injective p (AlgebraicClosure (ZMod p)))
  exact .of_isPullback _ _ (TauCeti.WittVector.padicIntHom p _) (IsFractionRing.lift hj)
    (IsLocalization.lift_comp _) g h φ s hX hY

/-- **The generic fibre of a smooth proper `ℤ`-scheme has everywhere Witt good reduction.** If `X`
is the base change of a smooth proper scheme `g : Y ⟶ Spec ℤ` along `Spec ℚ ⟶ Spec ℤ`, then `X`
has Witt good reduction at every prime. -/
theorem HasEverywhereWittGoodReduction.of_int {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℤ))
    [Smooth g] [IsProper g] (φ : X ⟶ Y)
    (hY : IsPullback φ f g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) :
    HasEverywhereWittGoodReduction f := by
  intro p _
  exact .of_isPullback (RingHom.id ℚ) (algebraMap ℤ ℚ) (Int.castRingHom _) (algebraMap ℚ _)
    (RingHom.ext_int _ _) g (𝟙 X) φ f (by simpa using IsPullback.of_id_fst) hY

variable {f' : X' ⟶ Spec (.of ℚ)}

/-- Witt good reduction at `p` transfers along an isomorphism of schemes over `ℚ`. -/
theorem HasWittGoodReductionAt.of_iso (e : X ≅ X') (he : e.hom ≫ f' = f)
    (hf' : HasWittGoodReductionAt f' p) : HasWittGoodReductionAt f p := by
  obtain ⟨a, -⟩ := id hf'
  obtain ⟨Y, g, hs, hp, XK, h, φ, s, hX, hY⟩ :=
    (hasWittGoodReductionAt_iff_exists_isPullback a).1 hf'
  refine (hasWittGoodReductionAt_iff_exists_isPullback a).2 ⟨Y, g, hs, hp, XK, h ≫ e.inv, φ, s,
    hX.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_, hY⟩ <;> simp [← he]

/-- Witt good reduction at `p` is invariant under isomorphism of schemes over `ℚ`. -/
theorem hasWittGoodReductionAt_iff_of_iso (e : X ≅ X') (he : e.hom ≫ f' = f) :
    HasWittGoodReductionAt f p ↔ HasWittGoodReductionAt f' p :=
  ⟨.of_iso e.symm (by simp [← he]), .of_iso e he⟩

/-- Everywhere Witt good reduction is invariant under isomorphism of schemes over `ℚ`. -/
theorem hasEverywhereWittGoodReduction_iff_of_iso (e : X ≅ X') (he : e.hom ≫ f' = f) :
    HasEverywhereWittGoodReduction f ↔ HasEverywhereWittGoodReduction f' :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ hasWittGoodReductionAt_iff_of_iso e he

/-- `Spec ℚ` has everywhere Witt good reduction, as the generic fibre of `Spec ℤ`. -/
theorem hasEverywhereWittGoodReduction_id : HasEverywhereWittGoodReduction (𝟙 (Spec (.of ℚ))) :=
  .of_int (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (IsPullback.of_vert_isIso ⟨by simp⟩)

end TauCeti.AlgebraicGeometry
