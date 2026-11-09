/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination

/-!
# Iterated extensions of centralizers

An *iterated extension of centralizers* (ICE) over a group `F` is a finite chain
`F = G₀ < G₁ < ⋯ < Gₘ` in which every `Gᵢ₊₁ = Gᵢ(uᵢ, ℤ^{nᵢ})` is an admissible extension of a
centralizer of `Gᵢ`: `uᵢ` is not a proper power and `nᵢ > 0`. The chain comes with the coefficient
inclusion `F →* Gₘ`, the composite of the inclusions of the successive steps.

Over a nonabelian free group `F` of finite rank, ICE groups are the model fully residually free
groups. Each of them is `F`-discriminated by `F`, and conversely, by a theorem of Kharlampovich and
Myasnikov which is not proved here, every finitely generated fully residually free group embeds in
one of them. This file sets up the chains over an arbitrary base group and proves the structural
facts that do not depend on the base. The coefficient inclusion is injective, and it is surjective
exactly for the empty chain, because every step is strict. It has a retraction. Chains can be
concatenated, and over a finitely generated base every ICE group is finitely generated.

Over a fully residually free base `F`, such as a free group, every ICE group is discriminated by
`F` over `F`, hence fully residually free. This follows by induction along the chain: each step
`Gᵢ₊₁ = Gᵢ(uᵢ, ℤ^{nᵢ})` is discriminated by `Gᵢ`, because `Gᵢ` is fully residually free, so CSA with
the big powers property (`TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`), and
discriminations compose.

## Main definitions

* `TauCeti.LimitGroup.ICE F G ι`: a chain of admissible extensions of centralizers from `F` to `G`,
  with coefficient inclusion `ι : F →* G`.
* `TauCeti.LimitGroup.ICE.single`: the one-step chain of an admissible extension of a centralizer.
* `TauCeti.LimitGroup.ICE.length`: the number of steps of a chain.
* `TauCeti.LimitGroup.ICE.append`: concatenation of a chain from `F` to `G` with one from `G` to
  `K`.

## Main results

* `TauCeti.LimitGroup.ICE.injective`: the coefficient inclusion of a chain is injective.
* `TauCeti.LimitGroup.ICE.range_eq_top_iff`: the coefficient inclusion is surjective exactly when
  the chain is empty.
* `TauCeti.LimitGroup.ICE.exists_retraction`: every ICE group over `F` retracts onto `F`.
* `TauCeti.LimitGroup.ICE.fg`: ICE groups over a finitely generated group are finitely generated.
* `TauCeti.LimitGroup.ICE.isDiscriminatedBy`: over a fully residually free group `F`, every ICE
  group is discriminated by `F` over `F`.
* `TauCeti.LimitGroup.ICE.isFullyResiduallyFree`: ICE groups over a fully residually free group are
  fully residually free.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II: Systems in
  triangular quasi-quadratic form and description of residually free groups*, J. Algebra 200
  (1998), §0.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

universe u

namespace TauCeti.LimitGroup

/-- An *iterated extension of centralizers* (ICE) over `F`: a finite chain
`F = G₀ < G₁ < ⋯ < Gₘ = G` with `Gᵢ₊₁ = Gᵢ(uᵢ, ℤ^{nᵢ})` an admissible extension of a centralizer
of `Gᵢ` (`IsAdmissibleCentralizerStep uᵢ nᵢ`), together with the coefficient inclusion
`ι : F →* G`. -/
inductive ICE (F : Type u) [Group F] : (G : Type u) → [Group G] → (F →* G) → Type (u + 1)
  /-- The empty chain: `F` over itself. -/
  | refl : ICE F F (MonoidHom.id F)
  /-- Extend the top of a chain by an admissible extension of a centralizer. -/
  | step {G : Type u} [Group G] {ι : F →* G} (c : ICE F G ι) {r : G} {n : ℕ}
      (h : IsAdmissibleCentralizerStep r n) :
      ICE F (CentralizerExt r n) ((CentralizerExt.of : G →* CentralizerExt r n).comp ι)

namespace ICE

variable {F G K : Type u} [Group F] [Group G] [Group K] {ι : F →* G}

/-- The chain consisting of a single admissible extension of a centralizer. For instance, over a
free group the extension of the centralizer of a basis element is admissible in every positive
rank (`isAdmissibleCentralizerStep_freeGroup_of`). -/
def single {r : F} {n : ℕ} (h : IsAdmissibleCentralizerStep r n) :
    ICE F (CentralizerExt r n) CentralizerExt.of :=
  step refl h

theorem single_eq_step_refl {r : F} {n : ℕ} (h : IsAdmissibleCentralizerStep r n) :
    single h = step refl h := (rfl)

/-- The number of steps of a chain. -/
def length {G : Type u} [Group G] {ι : F →* G} : ICE F G ι → ℕ
  | refl => 0
  | step c _ => c.length + 1

@[simp] theorem length_refl : (refl : ICE F F (.id F)).length = 0 := (rfl)

@[simp] theorem length_step (c : ICE F G ι) {r : G} {n : ℕ}
    (h : IsAdmissibleCentralizerStep r n) : (step c h).length = c.length + 1 := (rfl)

@[simp] theorem length_single {r : F} {n : ℕ} (h : IsAdmissibleCentralizerStep r n) :
    (single h).length = 1 := (rfl)

/-- Concatenate a chain from `F` to `G` with a chain from `G` to `K`. -/
def append (c : ICE F G ι) {K : Type u} [Group K] {j : G →* K} :
    ICE G K j → ICE F K (j.comp ι)
  | refl => c
  | step d h => step (c.append d) h

@[simp] theorem append_refl (c : ICE F G ι) : c.append refl = c := (rfl)

@[simp] theorem append_step (c : ICE F G ι) {j : G →* K} (d : ICE G K j) {r : K} {n : ℕ}
    (h : IsAdmissibleCentralizerStep r n) : c.append (step d h) = step (c.append d) h := (rfl)

@[simp] theorem length_append (c : ICE F G ι) {j : G →* K} (d : ICE G K j) :
    (c.append d).length = c.length + d.length := by
  induction d with
  | refl => rfl
  | step d h ih => simp [ih, Nat.add_assoc]

/-- The coefficient inclusion of an ICE chain is injective. -/
theorem injective (c : ICE F G ι) : Function.Injective ι := by
  induction c with
  | refl => exact Function.injective_id
  | step c h ih => exact CentralizerExt.of_injective.comp ih

/-- Every step of an ICE chain is strict: the coefficient inclusion is surjective exactly when the
chain is empty. -/
theorem range_eq_top_iff (c : ICE F G ι) : ι.range = ⊤ ↔ c.length = 0 := by
  induction c with
  | refl => simpa using MonoidHom.range_eq_top.2 Function.surjective_id
  | @step G _ ι c r n h ih =>
    simp only [length_step, Nat.add_one_ne_zero, iff_false]
    refine fun htop => CentralizerExt.range_of_ne_top (u := r) h.pos (eq_top_iff.2 ?_)
    rw [← htop]
    rintro _ ⟨x, rfl⟩
    exact ⟨ι x, rfl⟩

/-- Every ICE group over `F` retracts onto `F`: some homomorphism `G →* F` is a left inverse of
the coefficient inclusion. -/
theorem exists_retraction (c : ICE F G ι) : ∃ ρ : G →* F, ρ.comp ι = .id F := by
  induction c with
  | refl => exact ⟨.id _, rfl⟩
  | step c h ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨ρ.comp (CentralizerExt.retraction 0), ?_⟩
    rw [MonoidHom.comp_assoc, ← MonoidHom.comp_assoc _ CentralizerExt.of,
      CentralizerExt.retraction_comp_of, MonoidHom.id_comp, hρ]

/-- ICE groups over a finitely generated group are finitely generated. -/
theorem fg [Group.FG F] (c : ICE F G ι) : Group.FG G := by
  induction c with
  | refl => infer_instance
  | step c h ih => infer_instance

open GroupAlgGeom in
/-- **ICE groups are discriminated by their base.** Over a fully residually free group `F`, for
instance a free group, every ICE group `G` is discriminated by `F` over `F`: any finite family of
nonidentity elements of `G` survives under a single retraction `G →* F` of the coefficient
inclusion. -/
theorem isDiscriminatedBy (hF : IsFullyResiduallyFree F) (c : ICE F G ι) :
    IsDiscriminatedBy ι (.id F) := by
  induction c with
  | refl => exact .self _
  | @step G _ ι c r n h ih =>
    -- The top `G` of the shorter chain is fully residually free, so the new step is
    -- discriminated by `G`; compose with the discrimination of `G` by `F`.
    have hG := hF.of_isDiscriminatedBy ih
    have hstep := (CentralizerExt.isDiscriminatedBy (n := n) hG.isBP hG.isCSA h.ne_one).comp ι
    rw [MonoidHom.id_comp] at hstep
    exact hstep.trans ih

/-- ICE groups over a fully residually free group, for instance a free group, are fully residually
free. -/
theorem isFullyResiduallyFree (hF : IsFullyResiduallyFree F) (c : ICE F G ι) :
    IsFullyResiduallyFree G :=
  hF.of_isDiscriminatedBy (c.isDiscriminatedBy hF)

end ICE

end TauCeti.LimitGroup
