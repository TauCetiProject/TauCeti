/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Cone
public import TauCeti.Algebra.Homology.Periodic.HomotopicallyProjective

/-!
# Projective flags of periodic complexes

A cyclic cochain complex `K` has a **projective flag** when it admits a finite filtration
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ Fₘ = K` by subcomplexes, split in every degree, whose subquotients have
projective terms and zero differential. Choosing the degreewise splittings writes each term as
`Kⁱ = P₁ⁱ ⊕ ⋯ ⊕ Pₘⁱ` with a strictly triangular differential. We record the filtration one
step at a time: a complex with a projective flag is either zero, or a degreewise split extension
of a complex with a projective quotient carrying zero differential by a complex that already has
a projective flag (`HasProjectiveFlag`).

Projective flags are the periodic analogue of the free flags of Avramov, Buchweitz and Iyengar.
Every complex with a projective flag is homotopically projective
(`HasProjectiveFlag.isHomotopicallyProjective`): the layers with zero differential are
homotopically projective, and homotopically projective complexes are closed under degreewise split
extensions. Its terms are projective (`HasProjectiveFlag.projective_X`), but projectivity of the
terms does not suffice: the dual-number differential module of
`TauCeti.Algebra.Homology.Periodic.Examples` has a free term but no projective flag. Mapping
cones of maps from complexes with projective terms and zero differential into complexes with a
projective flag again have a projective flag (`HasProjectiveFlag.homotopyCofiber`).

No positive-period assumption is needed. At period zero, when `ZMod 0` is integer indexing, the
filtration describes bounded-length iterated extensions of complexes of projectives with zero
differential.

## Main definitions

* `TauCeti.PeriodicComplex.HasProjectiveFlag`: the complex has a finite projective flag.

## Main results

* `TauCeti.PeriodicComplex.HasProjectiveFlag.isHomotopicallyProjective`: a complex with a
  projective flag is homotopically projective.
* `TauCeti.PeriodicComplex.HasProjectiveFlag.projective_X`: its terms are projective.
* `TauCeti.PeriodicComplex.HasProjectiveFlag.homotopyCofiber`: mapping cones of maps from
  projective complexes with zero differential preserve projective flags.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of differential
  modules*, Inventiones Mathematicae **169** (2007), 1–35, Section 2.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Preadditive

variable [Preadditive C]

/-- A cyclic cochain complex has a **projective flag** when it is obtained from zero by finitely
many extensions, each split in every degree, by complexes with projective terms and zero
differential. The successive extensions form a finite filtration `0 = F₀ ⊆ ⋯ ⊆ Fₘ = K` by
subcomplexes, split in every degree, whose subquotients have projective terms and zero
differential. -/
inductive HasProjectiveFlag : CochainComplex C (ZMod n) → Prop
  /-- A zero complex has the empty projective flag. -/
  | of_isZero {K : CochainComplex C (ZMod n)} (hK : IsZero K) : HasProjectiveFlag K
  /-- Extending a complex with a projective flag, degreewise split, by a complex with projective
  terms and zero differential gives a complex with a projective flag. -/
  | extension (S : ShortComplex (CochainComplex C (ZMod n)))
      (hS : ∀ i, Nonempty (S.map (eval C (ComplexShape.up (ZMod n)) i)).Splitting)
      (h₁ : HasProjectiveFlag S.X₁) [∀ i, Projective (S.X₃.X i)]
      (hd : ∀ i j, S.X₃.d i j = 0) : HasProjectiveFlag S.X₂

/-- Having a projective flag is invariant under isomorphism of complexes. -/
theorem HasProjectiveFlag.of_iso {K L : CochainComplex C (ZMod n)} (e : K ≅ L)
    (hK : HasProjectiveFlag K) : HasProjectiveFlag L := by
  induction hK generalizing L with
  | of_isZero hK => exact .of_isZero (hK.of_iso e.symm)
  | extension S hS h₁ hd _ =>
    let S' := ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) (by simp)
    let φ : S ≅ S' := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp [S']) (by simp [S'])
    exact .extension S' (fun i ↦ (hS i).map fun s ↦
      s.ofIso ((eval C (ComplexShape.up (ZMod n)) i).mapShortComplex.mapIso φ)) h₁ hd

/-- A complex with projective terms and zero differential has a projective flag of length one. -/
theorem HasProjectiveFlag.of_d_eq_zero [HasZeroObject C] {K : CochainComplex C (ZMod n)}
    [∀ i, Projective (K.X i)] (hd : ∀ i j, K.d i j = 0) : HasProjectiveFlag K :=
  .extension (ShortComplex.mk (0 : 0 ⟶ K) (𝟙 K) zero_comp)
    (fun i ↦ ⟨.ofIsZeroOfIsIso _ ((eval C _ i).map_isZero (isZero_zero _))
      (inferInstanceAs (IsIso ((eval C _ i).map (𝟙 K))))⟩)
    (.of_isZero (isZero_zero _)) hd

/-- The mapping cone of a map from a complex with projective terms and zero differential to a
complex with a projective flag has a projective flag. -/
theorem HasProjectiveFlag.homotopyCofiber [HasBinaryBiproducts C] {X Y : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) [∀ i, Projective (X.X i)] (hd : ∀ i j, X.d i j = 0)
    (hY : HasProjectiveFlag Y) : HasProjectiveFlag (homotopyCofiber f) := by
  -- The quotient `X⟦1⟧` of the cone sequence has the terms of `X` and the negated differential.
  have (i : ZMod n) : Projective ((coneSequence f).X₃.X i) :=
    inferInstanceAs (Projective (X.X (i + ((1 : ℤ) : ZMod n))))
  exact .extension (coneSequence f) (fun i ↦ ⟨coneSequenceSplitting f i⟩) hY
    (fun i j ↦ (shiftFunctor_obj_d' X 1 i j).trans (by rw [hd, smul_zero]))

/-- The terms of a complex with a projective flag are projective. -/
theorem HasProjectiveFlag.projective_X {K : CochainComplex C (ZMod n)}
    (hK : HasProjectiveFlag K) (i : ZMod n) : Projective (K.X i) := by
  induction hK with
  | of_isZero hK => exact ((eval C _ i).map_isZero hK).projective
  | extension S hS _ _ ih =>
    -- Lift through the splitting `S.X₂ ≅ S.X₁ ⊕ S.X₃` one summand at a time.
    obtain ⟨s⟩ := hS i
    have : Projective (S.map (eval C _ i)).X₁ := ih
    have : Projective (S.map (eval C _ i)).X₃ := inferInstanceAs (Projective (S.X₃.X i))
    refine ⟨fun f e _ ↦ ⟨s.r ≫ Projective.factorThru ((S.map (eval C _ i)).f ≫ f) e +
      (S.map (eval C _ i)).g ≫ Projective.factorThru (s.s ≫ f) e, ?_⟩⟩
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, Projective.factorThru_comp,
      Projective.factorThru_comp, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      s.id]
    exact Category.id_comp f

end Preadditive

/-- A complex with a projective flag is homotopically projective: every map from it to an acyclic
complex is null-homotopic. -/
theorem HasProjectiveFlag.isHomotopicallyProjective [Abelian C] {K : CochainComplex C (ZMod n)}
    (hK : HasProjectiveFlag K) : IsHomotopicallyProjective K := by
  induction hK with
  | of_isZero hK => exact isHomotopicallyProjective_of_homotopy (.ofEq (hK.eq_of_src _ _))
  | extension S hS _ hd ih =>
    have := ih
    have := isHomotopicallyProjective_of_d_eq_zero hd
    exact .of_splitting S hS

end TauCeti.PeriodicComplex
