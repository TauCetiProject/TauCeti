/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.DimensionShift
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# The inflation-restriction sequence in every positive degree

Let `S` be a normal subgroup of a group `G` and `A` a representation of `G`. Inflation and
restriction form a complex

`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)`,

and if `Hⁱ(S, A) = 0` for `0 < i ≤ n`, it is exact and inflation is injective (Milne II 1.34).
Mathlib proves the case `n = 0`, where there is no hypothesis, as `groupCohomology.H1InfRes`.

The general case is by dimension shifting along the coinduced sequence

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0`.

Because `H¹(S, A) = 0`, taking `S`-invariants keeps it exact
(`shortExact_map_quotientToInvariantsFunctor`). The `S`-invariants of `Coind_⊥^G A` are coinduced
from the trivial subgroup of `G ⧸ S` (`Rep.quotientToInvariantsCoindBotIso`), so they have no
cohomology in positive degrees (`isZero_quotientToInvariants_coindBot_succ`). The connecting maps
of the three sequences over `G ⧸ S`, `G` and `S` are therefore isomorphisms. They are compatible
with inflation and restriction (`TauCeti.groupCohomology.δ_naturality`). So the complex for `A`
in degree `n + 2` is isomorphic to the complex for `dimensionShiftUp A` in degree `n + 1`, and
`dimensionShiftUp A` satisfies the vanishing hypothesis one degree lower.

When `Hⁱ(S, A)` vanishes also in degree `n + 1`, inflation is an isomorphism
(`isIso_infRes_f`). This is the form used for Tate's cohomological triviality criterion, where a
module is shown to be cohomologically trivial by induction along a normal series.

## Main definitions

* `TauCeti.groupCohomology.infRes`: the complex `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)`.

## Main statements

* `TauCeti.groupCohomology.mono_infRes_f`: inflation is injective.
* `TauCeti.groupCohomology.infRes_exact`: the inflation-restriction sequence is exact.
* `TauCeti.groupCohomology.isIso_infRes_f`: inflation is an isomorphism when `Hⁱ(S, A) = 0` for
  `0 < i ≤ n + 1`.
* `TauCeti.groupCohomology.map_one_succ`: the map along the trivial homomorphism vanishes in
  positive degrees.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, Proposition 1.34.
* J.-P. Serre, *Local Fields*, Chapter VII, §6, Proposition 5.
* `ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean` in `kbuzzard/ClassFieldTheory`,
  commit `ccc3323c6750abca25b49b35106f54eb3a398509`, states `inflation_restriction_mono` and
  `inflation_restriction_exact` with `sorry` proofs and sketches the same dimension-shifting
  argument. The proofs here are new.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- The map on cohomology along the trivial homomorphism vanishes in positive degrees, because it
factors through the cohomology of the trivial group. In degree one this is Mathlib's
`groupCohomology.map₁_one`. -/
theorem map_one_succ {H : Type u} [Group H] {B : Rep k H} {C : Rep k G}
    (φ : res (1 : G →* H) B ⟶ C) (n : ℕ) :
    map (1 : G →* H) φ (n + 1) = 0 := by
  have h := map_comp (1 : PUnit.{u + 1} →* H) (1 : G →* PUnit.{u + 1}) (𝟙 _) φ (n + 1)
  -- `1 : G →* H` factors through `PUnit`, whose positive-degree cohomology vanishes.
  have e : (resFunctor (1 : G →* PUnit.{u + 1})).map (𝟙 (res (1 : PUnit.{u + 1} →* H) B)) ≫ φ =
      φ := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp φ
  rw [e] at h
  -- `(1 : PUnit →* H).comp 1` is `1 : G →* H` by definition.
  refine (h : map (1 : G →* H) φ (n + 1) = _).trans ?_
  rw [(isZero_groupCohomology_succ_of_subsingleton _ n).eq_zero_of_tgt
    (map (1 : PUnit.{u + 1} →* H) (𝟙 _) (n + 1)), zero_comp]

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- Taking `S`-invariants is additive, so it maps short complexes of representations of `G` to
short complexes of representations of `G ⧸ S`. -/
instance : (quotientToInvariantsFunctor k S).Additive where

/-- **Taking invariants preserves a short exact sequence when `H¹` of its kernel vanishes.** If
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact and `H¹(S, X₁) = 0`, then so is
`0 ⟶ X₁^S ⟶ X₂^S ⟶ X₃^S ⟶ 0` as a sequence of representations of `G ⧸ S`. Only surjectivity on
the right needs the hypothesis. -/
theorem shortExact_map_quotientToInvariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology (res S.subtype X.X₁) 1)) :
    (X.map (quotientToInvariantsFunctor k S)).ShortExact := by
  -- Mathlib has no evaluation lemmas for `quotientToInvariantsFunctor` or for a short complex
  -- mapped by `forget₂`: both act on elements through the underlying maps of `X`, by definition.
  -- The type ascriptions below and the final `change` read the goals in that form.
  have hf := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hex : ∀ y : X.X₂, X.g.hom y = 0 → ∃ x, X.f.hom x = y :=
    (ShortComplex.moduleCat_exact_iff _).1 (hX.exact.map (forget₂ (Rep k G) (ModuleCat k)))
  refine
    { exact := (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun y hy => ?_
      mono_f := (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (hf (congrArg Subtype.val h))
      epi_g := (Rep.epi_iff_surjective _).2 fun z => ?_ }
  · obtain ⟨x, hx⟩ := hex y.1 (congrArg Subtype.val hy)
    refine ⟨⟨x, fun s => hf ?_⟩, Subtype.ext hx⟩
    have hx' : X.f.hom x = y.1 := hx
    have h2 : X.X₂.ρ s y.1 = y.1 := y.2 s
    exact (hom_comm_apply X.f s.1 x).trans (by rw [hx', h2])
  · obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective X.g).1 hX.epi_g z.1
    -- `s ↦ s • y - y` takes values in `X.X₁`, where it is a `1`-cocycle of `S`.
    have hc : ∀ s : S, ∃ x : X.X₁, X.f.hom x = X.X₂.ρ s y - y := fun s =>
      hex _ (by rw [map_sub, hom_comm_apply, hy]; exact sub_eq_zero.2 (z.2 s))
    choose c hc using hc
    have hcoc : c ∈ cocycles₁ (res S.subtype X.X₁) := by
      rw [mem_cocycles₁_iff]
      intro s t
      apply hf
      rw [res_obj_ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_add, hom_comm_apply, hc, hc,
        hc]
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
      abel
    -- It is a coboundary `s ↦ s • x - x`, and `y - x` is the required invariant lift.
    obtain ⟨x, hx⟩ := (H1π_eq_zero_iff (A := res S.subtype X.X₁) ⟨c, hcoc⟩).1
      ((ModuleCat.subsingleton_of_isZero h1).elim _ _)
    have hx' : ∀ s : S, X.X₁.ρ s x = c s + x := fun s =>
      sub_eq_iff_eq_add.1 (congr_fun hx s)
    have hgf : X.g.hom (X.f.hom x) = 0 := congrArg (fun φ => φ.hom x) X.zero
    refine ⟨⟨y - X.f.hom x, fun s => ?_⟩, Subtype.ext ?_⟩
    · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub, ← hom_comm_apply, hx', map_add, hc]
      abel
    · change X.g.hom (y - X.f.hom x) = z.1
      rw [map_sub, hy, hgf, sub_zero]

section Coinduced

variable (X : Type u) [AddCommGroup X] [Module k X]

/-- The `S`-invariants of `Coind_⊥^G X` have no cohomology over `G ⧸ S` in positive degrees: they
are coinduced from the trivial subgroup of `G ⧸ S`. -/
theorem isZero_quotientToInvariants_coindBot_succ (n : ℕ) :
    IsZero (groupCohomology ((coindBot k G X).quotientToInvariants S) (n + 1)) :=
  (_root_.groupCohomology.isZero_coindBot_succ X n).of_iso
    ((functor k (G ⧸ S) (n + 1)).mapIso (Rep.quotientToInvariantsCoindBotIso S X))

end Coinduced

/-- The **inflation-restriction complex** `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)` in degree
`n + 1`. In degree one it is Mathlib's `groupCohomology.H1InfRes`. -/
@[expose, simps X₁ X₂ X₃ f g]
def infRes (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) (n + 1)
  X₂ := groupCohomology A (n + 1)
  X₃ := groupCohomology (res S.subtype A) (n + 1)
  f := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) (n + 1)
  g := map S.subtype (𝟙 _) (n + 1)
  zero := by
    rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp_subtype S)
      (fun f φ => map f φ (n + 1)), map_one_succ]

-- The two statements are proved together, by induction on the degree.
private theorem mono_infRes_f_and_exact (n : ℕ) : ∀ A : Rep k G,
    (∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) →
      Mono (infRes A S n).f ∧ (infRes A S n).Exact := by
  induction n with
  | zero => exact fun A _ => ⟨inferInstanceAs (Mono (H1InfRes A S).f), H1InfRes_exact A S⟩
  | succ n ih =>
    intro A hA
    -- The upward dimension-shifting sequence `0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0`.
    let X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)
    have hX : X.ShortExact := by
      simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A
    have hXS : (X.map (resFunctor S.subtype)).ShortExact := by
      simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_res_shortExact A S.subtype
    have hY : (X.map (quotientToInvariantsFunctor k S)).ShortExact :=
      shortExact_map_quotientToInvariantsFunctor S hX (hA 0 n.succ_pos)
    obtain ⟨hmono, hexact⟩ := ih (dimensionShiftUp A) fun i hi =>
      (isZero_res_dimensionShiftUp_iff A S i).2 (hA (i + 1) (by omega))
    let e₁ : (infRes (dimensionShiftUp A) S n).X₁ ≅ (infRes A S (n + 1)).X₁ :=
      (map_cochainsFunctor_shortExact hY).δIso (n + 1) (n + 2) rfl
      (isZero_quotientToInvariants_coindBot_succ S A.V n)
      (isZero_quotientToInvariants_coindBot_succ S A.V (n + 1))
    let Φ : (X.map (quotientToInvariantsFunctor k S)).map (resFunctor (QuotientGroup.mk' S)) ⟶ X :=
      { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
        τ₂ := ofHom ((coindBot k G A.V).ρ.quotientToInvariants_lift S)
        τ₃ := ofHom ((dimensionShiftUp A).ρ.quotientToInvariants_lift S)
        comm₁₂ := by ext; rfl
        comm₂₃ := by ext; rfl }
    have h₁₂ : e₁.hom ≫ (infRes A S (n + 1)).f =
        (infRes (dimensionShiftUp A) S n).f ≫ (dimensionShiftUpIso A n).hom := by
      rw [dimensionShiftUpIso_hom]
      exact δ_naturality (QuotientGroup.mk' S) hY hX Φ (n + 1) (n + 2) rfl
    have h₂₃ : (dimensionShiftUpIso A n).hom ≫ (infRes A S (n + 1)).g =
        (infRes (dimensionShiftUp A) S n).g ≫ (dimensionShiftUpResIso A S n).hom := by
      rw [dimensionShiftUpIso_hom, dimensionShiftUpResIso_hom]
      exact δ_naturality S.subtype hX hXS (𝟙 _) (n + 1) (n + 2) rfl
    have hf : (infRes A S (n + 1)).f =
        e₁.inv ≫ (infRes (dimensionShiftUp A) S n).f ≫ (dimensionShiftUpIso A n).hom := by
      rw [← h₁₂]
      exact (e₁.inv_hom_id_assoc _).symm
    refine ⟨?_, ShortComplex.exact_of_iso ?_ hexact⟩
    · rw [hf]
      have : Mono (dimensionShiftUpIso A n).hom := IsIso.mono_of_iso _
      -- Instance search does not see through `(infRes _ S n).X₂ = Hⁿ⁺¹(G, _)`, so the
      -- composite is assembled by hand.
      exact @mono_comp _ _ _ _ _ e₁.inv _ _ (@mono_comp _ _ _ _ _ _ hmono _ this)
    · exact ShortComplex.isoMk e₁ (dimensionShiftUpIso A n) (dimensionShiftUpResIso A S n) h₁₂ h₂₃

variable {S}

/-- **Inflation is injective** (Milne II 1.34): if `Hⁱ(S, A) = 0` for `0 < i ≤ n`, then inflation
`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A)` is a monomorphism. -/
theorem mono_infRes_f (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    Mono (infRes A S n).f :=
  (mono_infRes_f_and_exact S n A hA).1

/-- **The inflation-restriction sequence is exact** (Milne II 1.34): if `Hⁱ(S, A) = 0` for
`0 < i ≤ n`, then `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)` is exact. -/
theorem infRes_exact (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    (infRes A S n).Exact :=
  (mono_infRes_f_and_exact S n A hA).2

/-- **Inflation is an isomorphism** when `Hⁱ(S, A) = 0` for `0 < i ≤ n + 1`: then
`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A)` is injective, and surjective because restriction lands in
`Hⁿ⁺¹(S, A) = 0`. -/
theorem isIso_infRes_f (n : ℕ)
    (hA : ∀ i ≤ n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    IsIso (infRes A S n).f :=
  have := mono_infRes_f A n fun i hi => hA i hi.le
  have := (infRes_exact A n fun i hi => hA i hi.le).epi_f ((hA n le_rfl).eq_of_tgt _ _)
  isIso_of_mono_of_epi _

end TauCeti.groupCohomology
