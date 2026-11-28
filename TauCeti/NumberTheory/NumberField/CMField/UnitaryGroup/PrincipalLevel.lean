/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel.NhdsBasis
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ModEq
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Principal levels of the finite adelic unitary group

Let `E` be a CM field, `Ô` its integral finite adeles, and `G_f = U(1_n)(𝔸_f)` the finite adelic
unitary group of a finite index type `ι` of size `n`, with its subgroup `K₀ = G_f ∩ GL_n(Ô)`
(`TauCeti.integralAdelicUnitaryGroup`). For an ideal `N` of `𝓞_E`, write `NÔ` for its completion
`IsDedekindDomain.FiniteAdeleRing.completedIdeal E N`. The **principal level** of `N` is

`K(N) = {g ∈ K₀ : g ≡ 1 mod NÔ}`,

the trace on `G_f` of the kernel of reduction `GL_n(Ô) → GL_n(Ô ⧸ NÔ)`, read in `GL_n(𝔸_f)`
through `IsDedekindDomain.FiniteAdeleRing.integralGL`. For `0 ≠ a ∈ 𝓞_E`, the principal level
`K(a)` of the element `a` is `K(a 𝓞_E)`; no generator is needed, so nonprincipal ideals are
allowed.

For `N ≠ ⊥` the principal level is a level of `G_f` (an open subgroup contained in `K₀`), it
shrinks as `N` does (so `K(b) ⊆ K(a)` when `a ∣ b`), and its index in `K₀` is at most
`N(N) ^ (n²)`, where `N(N) = [𝓞_E : N]` is the absolute norm: reduction embeds `K₀ ⧸ K(N)` in
`GL_n(Ô ⧸ NÔ)`, and `Ô ⧸ NÔ ≅ 𝓞_E ⧸ N`. The principal levels form a basis of neighbourhoods of `1`
in `G_f`, and already those of the ideals `M 𝓞_E` for integers `M ≥ 1` do: every neighbourhood of
`1` in `G_f` contains `K(M)` for some integer `M ≥ 1`. Principal levels thus give, inside any given
level, a level of a standard shape.

## Main definitions

* `TauCeti.principalUnitaryLevel E ι N`: the principal level `K(N)`.

## Main results

* `TauCeti.mem_principalUnitaryLevel_iff`: `g ∈ K(N)` exactly when `g` is the image of a matrix
  `h ∈ GL_n(Ô)` with `h ≡ 1 mod NÔ` entrywise.
* `TauCeti.principalUnitaryLevel_le_integralAdelicUnitaryGroup`, `principalUnitaryLevel_mono`,
  `principalUnitaryLevel_top`, `principalUnitaryLevel_bot`: `K(N) ⊆ K₀`, monotonicity in `N`,
  `K(𝓞_E) = K₀` and `K(0) = 1`.
* `TauCeti.isUnitaryLevel_principalUnitaryLevel`: for `N ≠ ⊥`, `K(N)` is a level.
* `TauCeti.hasBasis_nhds_one_principalUnitaryLevel`,
  `TauCeti.hasBasis_nhds_one_principalUnitaryLevel_natCast`: the principal levels of the nonzero
  ideals, and already those of the positive integers, form a basis of neighbourhoods of `1` in
  `G_f`.
* `TauCeti.relIndex_principalUnitaryLevel_le`: `[K₀ : K(N)] ≤ N(N) ^ (n²)`.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.
* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §4.

## Attribution

The principal level and the statements on it follow `New.principalLevel`,
`New.isOpen_principalLevel`, `New.principalLevel_le_of_dvd`, `New.exists_principalLevel_subset`
and `New.relIndex_principalLevel_le` in the file `src/Lib/Adelic/Unitary/CongruenceLevels.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] (ι : Type*) [Fintype ι]
  [DecidableEq ι]

/-- The **principal level** `K(N) = {g ∈ K₀ : g ≡ 1 mod NÔ}` of an ideal `N` of `𝓞_E` in the finite
adelic unitary group `G_f` of a CM field `E`: the elements of `G_f` that are images under
`integralGL : GL_n(Ô) → GL_n(𝔸_f)` of matrices in the kernel of reduction
`GL_n(Ô) → GL_n(Ô ⧸ NÔ)`, where `NÔ` is the completion of `N`. -/
def principalUnitaryLevel (N : Ideal (𝓞 E)) : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  ((GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (FiniteAdeleRing.completedIdeal E N))).ker.map
    (FiniteAdeleRing.integralGL E ι)).subgroupOf (finiteAdelicUnitaryGroup E ι)

variable {E ι}

/-- The principal level `K(N)` is the trace on `G_f` of the image in `GL_n(𝔸_f)` of the kernel of
reduction `GL_n(Ô) → GL_n(Ô ⧸ NÔ)`. -/
theorem principalUnitaryLevel_def (N : Ideal (𝓞 E)) :
    principalUnitaryLevel E ι N =
      ((GeneralLinearGroup.map (n := ι)
          (Ideal.Quotient.mk (FiniteAdeleRing.completedIdeal E N))).ker.map
        (FiniteAdeleRing.integralGL E ι)).subgroupOf (finiteAdelicUnitaryGroup E ι) :=
  (rfl)

/-- `g ∈ G_f` lies in the principal level `K(N)` exactly when it is the image of a matrix
`h ∈ GL_n(Ô)` congruent to `1` modulo `NÔ` entrywise. -/
theorem mem_principalUnitaryLevel_iff {N : Ideal (𝓞 E)} {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ principalUnitaryLevel E ι N ↔
      ∃ h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E),
        FiniteAdeleRing.integralGL E ι h = g ∧
          ∀ i j, (h : Matrix ι ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) i j -
            (1 : Matrix ι ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) i j ∈
              FiniteAdeleRing.completedIdeal E N := by
  simp only [principalUnitaryLevel_def, Subgroup.mem_subgroupOf, Subgroup.mem_map,
    GeneralLinearGroup.mem_ker_map_quotientMk_iff]
  exact ⟨fun ⟨h, hh, hg⟩ ↦ ⟨h, hg, hh⟩, fun ⟨h, hg, hh⟩ ↦ ⟨h, hh, hg⟩⟩

/-- At the principal level `(a)`, each column of the finite adelic matrix is congruent
modulo `a` to the corresponding column of the identity. -/
theorem modEq_apply_of_mem_principalUnitaryLevel {a : 𝓞 E} {g : finiteAdelicUnitaryGroup E ι}
    (hg : g ∈ principalUnitaryLevel E ι (Ideal.span {a})) (i j : ι) :
    FiniteAdeleRing.ModEq a ((↑(g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j)
      ((1 : Matrix ι ι 𝔸ᶠ[E]) i j) := by
  obtain ⟨h, hh, hc⟩ := mem_principalUnitaryLevel_iff.mp hg
  have h₁ : (↑((1 : Matrix ι ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) i j) : 𝔸ᶠ[E]) =
      (1 : Matrix ι ι 𝔸ᶠ[E]) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [← hh, FiniteAdeleRing.integralGL_apply, ← h₁]
  exact (FiniteAdeleRing.modEq_iff_sub_mem_completedIdeal _ _).mpr (hc i j)

variable (E ι) in
/-- A principal level is contained in `K₀`. -/
theorem principalUnitaryLevel_le_integralAdelicUnitaryGroup (N : Ideal (𝓞 E)) :
    principalUnitaryLevel E ι N ≤ integralAdelicUnitaryGroup E ι :=
  fun _ hg ↦ mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.2 <|
    let ⟨h, hh, _⟩ := mem_principalUnitaryLevel_iff.1 hg
    ⟨h, hh⟩

variable (E ι) in
/-- The principal level `K(N)` grows with `N`; in particular `K(b) ⊆ K(a)` when `a ∣ b`. -/
theorem principalUnitaryLevel_mono : Monotone (principalUnitaryLevel E ι) :=
  fun _ _ hNN' ↦ Subgroup.subgroupOf_mono _
    (Subgroup.map_mono (GeneralLinearGroup.ker_map_quotientMk_mono
      (FiniteAdeleRing.completedIdeal_mono E hNN')))

variable (E ι) in
/-- The principal level of the unit ideal is `K₀`. -/
@[simp]
theorem principalUnitaryLevel_top :
    principalUnitaryLevel E ι ⊤ = integralAdelicUnitaryGroup E ι := by
  refine le_antisymm (principalUnitaryLevel_le_integralAdelicUnitaryGroup E ι ⊤) fun g hg ↦ ?_
  obtain ⟨h, hh⟩ := mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.1 hg
  exact mem_principalUnitaryLevel_iff.2 ⟨h, hh, fun i j ↦ by
    simp only [FiniteAdeleRing.completedIdeal_top, Submodule.mem_top]⟩

variable (E ι) in
/-- The principal level of the zero ideal is trivial. -/
@[simp]
theorem principalUnitaryLevel_bot : principalUnitaryLevel E ι ⊥ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_
  obtain ⟨h, hgh, hh⟩ := mem_principalUnitaryLevel_iff.1 hg
  have h1 : h = 1 := GeneralLinearGroup.ext fun i j ↦ by
    simpa [FiniteAdeleRing.completedIdeal_bot, sub_eq_zero] using hh i j
  exact Subtype.ext (by rw [← hgh, h1, map_one, OneMemClass.coe_one])

variable (E ι) in
/-- **The principal levels form a basis of neighbourhoods of `1` in `G_f`**, as `N` runs over the
nonzero ideals of `𝓞_E`. -/
theorem hasBasis_nhds_one_principalUnitaryLevel :
    (𝓝 (1 : finiteAdelicUnitaryGroup E ι)).HasBasis (fun N : Ideal (𝓞 E) ↦ N ≠ ⊥) fun N ↦
      (principalUnitaryLevel E ι N : Set (finiteAdelicUnitaryGroup E ι)) := by
  rw [nhds_subtype, OneMemClass.coe_one]
  exact (FiniteAdeleRing.hasBasis_nhds_one_map_ker_integralGL E ι).comap _

variable (E ι) in
/-- **The principal levels of the positive integers form a basis of neighbourhoods of `1` in
`G_f`**: every neighbourhood of `1` in `G_f` contains `K(M) = {g ∈ K₀ : g ≡ 1 mod MÔ}` for some
integer `M ≥ 1`. -/
theorem hasBasis_nhds_one_principalUnitaryLevel_natCast :
    (𝓝 (1 : finiteAdelicUnitaryGroup E ι)).HasBasis (fun M : ℕ ↦ M ≠ 0) fun M ↦
      (principalUnitaryLevel E ι (Ideal.span {(M : 𝓞 E)}) :
        Set (finiteAdelicUnitaryGroup E ι)) := by
  rw [nhds_subtype, OneMemClass.coe_one]
  exact (FiniteAdeleRing.hasBasis_nhds_one_map_ker_integralGL_natCast E ι).comap _

/-- For `N ≠ ⊥`, the principal level `K(N)` is open in `G_f`: it is a subgroup and, by
`hasBasis_nhds_one_principalUnitaryLevel`, a neighbourhood of `1`. -/
theorem isOpen_principalUnitaryLevel {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) :
    IsOpen (principalUnitaryLevel E ι N : Set (finiteAdelicUnitaryGroup E ι)) :=
  Subgroup.isOpen_of_mem_nhds _ ((hasBasis_nhds_one_principalUnitaryLevel E ι).mem_of_mem hN)

/-- For `N ≠ ⊥`, the principal level `K(N)` is a level: an open subgroup of `G_f` contained in
`K₀`. -/
theorem isUnitaryLevel_principalUnitaryLevel {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) :
    IsUnitaryLevel (principalUnitaryLevel E ι N) :=
  ⟨principalUnitaryLevel_le_integralAdelicUnitaryGroup E ι N, isOpen_principalUnitaryLevel hN⟩

/-- **The index of a principal level.** For `N ≠ ⊥`, `[K₀ : K(N)] ≤ N(N) ^ (n²)`, where `N(N)` is
the absolute norm of `N` and `n = |ι|`: reduction modulo `NÔ` embeds `K₀ ⧸ K(N)` in
`GL_n(Ô ⧸ NÔ)`, which has at most `|Ô ⧸ NÔ| ^ (n²) = N(N) ^ (n²)` elements. -/
theorem relIndex_principalUnitaryLevel_le {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) :
    (principalUnitaryLevel E ι N).relIndex (integralAdelicUnitaryGroup E ι) ≤
      Ideal.absNorm N ^ (Fintype.card ι ^ 2) := by
  set Q := FiniteAdeleRing.integralAdeles (𝓞 E) E ⧸ FiniteAdeleRing.completedIdeal E N
  have : Finite (𝓞 E ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
  have : Finite Q := FiniteAdeleRing.finite_quotient_completedIdeal E hN
  -- Reduction modulo `NÔ` on `K₀`, read in the unitary subgroup of `GL_n(Ô)`.
  let red : integralAdelicUnitaryGroup E ι →* GL ι Q :=
    (GeneralLinearGroup.map (Ideal.Quotient.mk (FiniteAdeleRing.completedIdeal E N))).comp
      ((unitarySubgroup _).subtype.comp (integralAdelicUnitaryGroupEquiv E ι).symm.toMonoidHom)
  -- Its kernel is `K(N)`, read in `K₀`.
  have hker : (principalUnitaryLevel E ι N).subgroupOf (integralAdelicUnitaryGroup E ι) =
      red.ker := by
    ext g
    set h := (integralAdelicUnitaryGroupEquiv E ι).symm g
    have hg : FiniteAdeleRing.integralGL E ι (h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) =
        ((g : finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E]) := by
      rw [← coe_integralAdelicUnitaryGroupEquiv, MulEquiv.apply_symm_apply]
    rw [Subgroup.mem_subgroupOf, principalUnitaryLevel_def, Subgroup.mem_subgroupOf,
      Subgroup.mem_map, ← hg, MonoidHom.mem_ker]
    simp only [(FiniteAdeleRing.integralGL_injective E ι).eq_iff, exists_eq_right,
      MonoidHom.mem_ker, red, h, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  have hQ : Nat.card Q = Ideal.absNorm N := by
    rw [Ideal.absNorm_eq_natCard,
      Nat.card_congr (FiniteAdeleRing.quotientEquivQuotientCompletedIdeal E hN).toEquiv]
  calc (principalUnitaryLevel E ι N).relIndex (integralAdelicUnitaryGroup E ι)
      = Nat.card red.range := by rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    _ ≤ Nat.card (GL ι Q) := Subgroup.card_le_card_group _
    _ ≤ Nat.card (Matrix ι ι Q) := Nat.card_le_card_of_injective _ Units.val_injective
    _ = Ideal.absNorm N ^ (Fintype.card ι ^ 2) := by
      rw [card_matrix, hQ, Nat.card_eq_fintype_card, sq]

end TauCeti
