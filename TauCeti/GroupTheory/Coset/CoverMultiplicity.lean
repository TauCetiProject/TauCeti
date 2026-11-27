/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.Index.PrimePart

/-!
# Cover multiplicities of a set of cosets

Let `S`, `A` and `J` be subgroups of a group `G` and `T` a set of left cosets of `J`. The
translates `r • T`, `r ∈ S`, cover the union of the `S`-orbits meeting `T`, and the translates by
the elements of one class `r (S ∩ A)` agree when `T` is stable under `S ∩ A`. The
**cover multiplicity** of a coset `t` counts the classes of `r ∈ S` modulo `S ∩ A` with
`r⁻¹ • t ∈ T`, that is the translates of `T` through `t` counted modulo `S ∩ A`; it is `0` when
there are infinitely many.

For `T` stable under `S ∩ A`, the multiplicity `mult(t)` counts the classes `r (S ∩ A)` of
`r ∈ S` with `t ∈ r • T`, and it is constant along `S`-orbits (`Subgroup.coverMultiplicity_smul`),
so dividing by it normalizes the translate cover pointwise: at a coset `t` of finite, nonzero
multiplicity, the sum of `1_T(r⁻¹ • t) / mult(r⁻¹ • t)` over all classes `r (S ∩ A)` is `1`. This
identity, a direct consequence of the definition and `Subgroup.coverMultiplicity_smul`, is the
only statement about the weights `1 / mult(t)` that this file supports.

The integral formula that uses these weights, ThetaLiftChainsAndTheSeesawIdentity §3.1 (c) of the
roadmap, is a later application and is not proved here. There `S` is the finite part `R_f` of a
Bessel subgroup `R`, and the integral of a function `f` over `R(F)\U(V)(𝔸)` is a constant times
the sum of `b(t) / mult(t)` over `t ∈ T` only under further hypotheses on `f`: it vanishes at
every `g` whose finite part has multiplicity `0`, and its orbit averages `∫_{[R]} f(r t) dr`
factor as an index `[K° : J]` times an archimedean factor `a(t_∞)` times `b(t_f)` whenever
`t_f J ∈ T`, for a function `b` on the cosets of `J`. The summands are the values of `b`, which
descend to `J`-cosets, not raw values of `f`.

When the points of `T` in the `S`-orbit of `t` are exactly the `(S ∩ A)`-orbit of `t`, the
multiplicity of `t` is the relative index `A.relIndex H`, the index of `A ∩ H` in the stabiliser
`H` of `t` in `S`. If it is finite (nonzero) and every element of `H` has a `q`-power power in
`A`, it divides a power of `q`, by `Subgroup.exists_index_dvd_pow_of_forall_exists_pow_pow_mem`.

The construction of finite sets `T` with these properties, for compact open subgroups `A` and `J`
of a topological group, is in `TauCeti.Topology.Algebra.Group.CoverMultiplicity`.

## Main definitions

* `Subgroup.coverMultiplicity S A T t`: the number of classes of `r ∈ S` modulo `S ∩ A` with
  `r⁻¹ • t ∈ T`, and `0` if there are infinitely many.

## Main results

* `Subgroup.coverMultiplicity_smul`: the cover multiplicity is constant on `S`-orbits.
* `Subgroup.coverMultiplicity_eq_relIndex`: if the points of `T` in the `S`-orbit of `t` are
  exactly the `(S ∩ A)`-orbit of `t`, the cover multiplicity of `t` is the relative index
  `A.relIndex H`, the index of `A ∩ H` in the stabiliser `H` of `t` in `S`.
* `Subgroup.exists_coverMultiplicity_dvd_pow`: in that situation, if the multiplicity is finite
  (nonzero) and every element of `H` has a `q`-power power in `A`, the multiplicity divides a
  power of `q`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, for the class sets of
  groups compact at infinity weighted by inverse orders of stabilisers.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/UpperBound/Seesaw/IntegralAsCosetSum.lean` (declarations
  `New.Seesaw.coverMultiplicity` and `New.Seesaw.coverMultiplicity_smul`); Apache 2.0, Copyright
  2026 Anthropic, PBC. The definition and the description of the multiplicity as the index of a
  stabiliser follow the method of this proof.
-/

public section

open MulAction

namespace Subgroup

variable {G : Type*} [Group G] (S A : Subgroup G) {J : Subgroup G} (T : Set (G ⧸ J))

/-- The **cover multiplicity** of a left coset `t` of `J`, for subgroups `S`, `A` and a set `T` of
left cosets of `J`: the number of classes of `r ∈ S` modulo `S ∩ A` with `r⁻¹ • t ∈ T`, and `0`
if there are infinitely many. The class `r (S ∩ A)` of `r ∈ S` is recorded by the coset `r A`,
since `r (S ∩ A) ↦ r A` is injective. When `T` is stable under `S ∩ A`, the condition
`r⁻¹ • t ∈ T` depends only on the class of `r`. -/
noncomputable def coverMultiplicity (t : G ⧸ J) : ℕ :=
  (((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T}).ncard

/-- The cover multiplicity is the number of cosets `r A` of the elements `r ∈ S` with
`r⁻¹ • t ∈ T`. -/
theorem coverMultiplicity_def (t : G ⧸ J) :
    S.coverMultiplicity A T t = (((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T}).ncard :=
  (rfl)

variable {S A T}

/-- **The cover multiplicity is constant on `S`-orbits.** -/
@[simp]
theorem coverMultiplicity_smul {s : G} (hs : s ∈ S) (t : G ⧸ J) :
    S.coverMultiplicity A T (s • t) = S.coverMultiplicity A T t := by
  -- Left multiplication by `s` carries the classes counted at `t` onto those counted at `s • t`.
  have hset : {r | r ∈ S ∧ r⁻¹ • s • t ∈ T} = (s * ·) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T} := by
    ext r
    simp [Set.image_mul_left, mul_smul, mul_mem_cancel_left (inv_mem hs)]
  have hcomp : (fun r ↦ ((s * r : G) : G ⧸ A)) = (s • ·) ∘ ((↑) : G → G ⧸ A) := by
    ext
    simp
  rw [coverMultiplicity_def, coverMultiplicity_def, hset, Set.image_image, hcomp, Set.image_comp,
    Set.ncard_image_of_injective _ (MulAction.injective s)]

/-- **The cover multiplicity as the index of a stabiliser.** If the points of `T` in the `S`-orbit
of `t` are exactly the points of the `(S ∩ A)`-orbit of `t`, then the cover multiplicity of `t` is
the index of `A ∩ H` in the stabiliser `H = S ∩ Stab(t)` of `t` in `S`. -/
theorem coverMultiplicity_eq_relIndex {t : G ⧸ J}
    (hT : ∀ s ∈ S, s • t ∈ T ↔ ∃ a ∈ S ⊓ A, a • t = s • t) :
    S.coverMultiplicity A T t = A.relIndex (S ⊓ stabilizer G t) := by
  set H := S ⊓ stabilizer G t
  -- The translates of `T` through `t` are those by the elements of `H (S ∩ A)`.
  have himage : ((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T} = (↑) '' (H : Set G) := by
    ext q
    constructor
    · rintro ⟨r, ⟨hrS, hrt⟩, rfl⟩
      obtain ⟨a, ha, hat⟩ := (hT r⁻¹ (inv_mem hrS)).1 hrt
      refine ⟨r * a, ⟨mul_mem hrS ha.1, ?_⟩, QuotientGroup.eq.2 (by simpa using ha.2)⟩
      exact mem_stabilizer_iff.2 (by rw [mul_smul, hat, smul_inv_smul])
    · rintro ⟨h, ⟨hhS, hht⟩, rfl⟩
      refine ⟨h, ⟨hhS, ?_⟩, rfl⟩
      rw [inv_smul_eq_iff.2 (mem_stabilizer_iff.1 hht).symm]
      simpa using (hT 1 S.one_mem).2 ⟨1, one_mem _, rfl⟩
  -- Orbit–stabiliser for `H` acting on `G ⧸ A` at the coset of `1`.
  have horbit : ((↑) : G → G ⧸ A) '' (H : Set G) = orbit H ((1 : G) : G ⧸ A) := by
    ext q
    simp [mem_orbit_iff, Subgroup.smul_def, eq_comm]
  rw [coverMultiplicity_def, himage, horbit, ← index_stabilizer, ← stabilizer_subgroupOf,
    stabilizer_quotient, relIndex]

/-- **The cover multiplicity divides a power of `q`.** If the points of `T` in the `S`-orbit of
`t` are exactly the points of the `(S ∩ A)`-orbit of `t`, the cover multiplicity of `t` is finite
and nonzero, and every element `g` of the stabiliser of `t` in `S` has a power `g ^ q ^ n` in `A`,
then the cover multiplicity of `t` divides a power of `q`. -/
theorem exists_coverMultiplicity_dvd_pow {t : G ⧸ J}
    (hT : ∀ s ∈ S, s • t ∈ T ↔ ∃ a ∈ S ⊓ A, a • t = s • t)
    (hne : S.coverMultiplicity A T t ≠ 0) {q : ℕ}
    (hq : ∀ g ∈ S ⊓ stabilizer G t, ∃ n : ℕ, g ^ q ^ n ∈ A) :
    ∃ n : ℕ, S.coverMultiplicity A T t ∣ q ^ n := by
  rw [coverMultiplicity_eq_relIndex hT] at hne ⊢
  have : (A.subgroupOf (S ⊓ stabilizer G t)).FiniteIndex := ⟨hne⟩
  exact (A.subgroupOf _).exists_index_dvd_pow_of_forall_exists_pow_pow_mem fun g ↦ by
    simpa [mem_subgroupOf] using hq g g.property

end Subgroup
