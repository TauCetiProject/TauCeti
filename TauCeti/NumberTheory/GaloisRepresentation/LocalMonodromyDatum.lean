/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.GroupAction.ConjAct
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# Local monodromy data

Let `k` be a nonarchimedean local field with residue field `𝔽_q`, and `ℓ` a prime different from
the residue characteristic. Grothendieck's monodromy theorem and the weight–monodromy conjecture
only use four pieces of structure on the absolute Galois group `G_k`: the inertia subgroup
`I_k`, the `ℓ`-adic tame character `t_ℓ : I_k → ℚ_ℓ`, the coset of geometric Frobenius lifts, and
the integer `q`, linked by the twist `t_ℓ(Φ σ Φ⁻¹) = q⁻¹ t_ℓ(σ)` for a geometric Frobenius `Φ`.
Following Scholze, this file axiomatizes that structure on an arbitrary profinite group, so that
purity can be defined relative to it and transported between groups that are not Galois groups of
discretely valued fields (such as the Galois group of a perfectoid field).

A **local monodromy datum** `D` on a profinite group `H` consists of

* a closed normal subgroup `I`, the *inertia*;
* a continuous homomorphism `t : I → ℚ_ℓ`, the *tame character*, which is not identically zero;
* an integer `q ≥ 2` prime to `ℓ`;
* a coset `Fr = Φ I` of `I`, the *Frobenius coset*,

such that `H / I ≅ ℤ̂` as topological groups by an isomorphism sending `Fr` to the generator, and
`t(Φ σ Φ⁻¹) = q⁻¹ t(σ)` for `Φ ∈ Fr` and `σ ∈ I`. The tame character is written
multiplicatively, as a continuous homomorphism to `Multiplicative ℚ_[ℓ]`, in the same way as
`TauCeti.inertiaPadicTameCharacter`. The latter takes values in `ℤ_ℓ(1)` rather than `ℚ_ℓ`, so
the tame character of a Galois group depends on a trivialization `ℤ_ℓ(1) ≅ ℤ_ℓ`, which is
determined only up to a unit.

Data are *marked*: an isomorphism `D → D'` of local monodromy data is a topological group
isomorphism carrying inertia onto inertia and the Frobenius coset onto the Frobenius coset, with
the same `q`, and with `t' ∘ α = c t` for a single constant `c ∈ ℚ_ℓˣ`. Rescaling the tame
character by `c` gives the datum `c • D`, isomorphic to `D` through the identity with constant
`c`.

## Main definitions

* `TauCeti.LocalMonodromyDatum ℓ H`: local monodromy data on the profinite group `H`.
* `TauCeti.LocalMonodromyDatum.frobenius`: the Frobenius coset, as a subset of `H`.
* The action of `ℚ_[ℓ]ˣ` on `LocalMonodromyDatum ℓ H` by rescaling the tame character.
* `TauCeti.LocalMonodromyDatum.IsIso D D' α c`: `α` is an isomorphism of local monodromy data
  `D → D'` with constant `c`.

## Main results

* `TauCeti.LocalMonodromyDatum.mem_frobenius_iff_inv_mul_mem`: the Frobenius coset is a single
  coset of inertia.
* `TauCeti.LocalMonodromyDatum.tame_conj_of_coe_eq_frobClass_pow`: conjugation by an element of
  the class `frobClass ^ n` divides the tame character by `q ^ n`.
* `TauCeti.LocalMonodromyDatum.one_notMem_frobenius`: the Frobenius coset is not inertia itself.
* `TauCeti.LocalMonodromyDatum.denseRange_zpow_frobClass`: the class of Frobenius topologically
  generates `H / I`.
* `TauCeti.LocalMonodromyDatum.exists_tame_ne_one_of_isOpen`: the tame character is not
  identically zero on any open subgroup of inertia.
* `TauCeti.LocalMonodromyDatum.IsIso.refl`, `IsIso.symm`, `IsIso.trans`: identity, inverse and
  composition of isomorphisms, with constants `1`, `c⁻¹` and `c' * c`.
* `TauCeti.LocalMonodromyDatum.isIso_refl_smul`, `isIso_smul_refl`: the identity is an isomorphism
  `D → c • D` with constant `c`, and `c • D → D` with constant `c⁻¹`.
* `TauCeti.LocalMonodromyDatum.IsIso.smul_right`, `IsIso.smul_left`: rescaling the target or the
  source of an isomorphism with constant `c` by `c'` changes the constant to `c' * c` or
  `c * c'⁻¹`.
* `TauCeti.LocalMonodromyDatum.IsIso.const_eq`, `isIso_refl_smul_iff`: the constant of an
  isomorphism is determined by the underlying group isomorphism.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §9: Proposition 9.1,
  Definition/Proposition 9.2 and the proof of Theorem 9.6.
-/

public section

noncomputable section

namespace TauCeti

universe u v w

/-- **A local monodromy datum** on a profinite group `H`, for a prime `ℓ`: a closed normal
subgroup `inertia`, a continuous tame character `tame : inertia → ℚ_ℓ` (written multiplicatively)
that is not identically zero, an integer `q ≥ 2` prime to `ℓ`, and a class `frobClass` in
`H ⧸ inertia`, whose elements form the Frobenius coset. The quotient `H ⧸ inertia` is required to
be isomorphic to `ℤ̂` as a topological group by an isomorphism sending `frobClass` to the
generator, and conjugation by a Frobenius element `Φ` scales the tame character by `q⁻¹`:
`t(Φ σ Φ⁻¹) = q⁻¹ t(σ)`. For a nonarchimedean local field `k` with residue field `𝔽_q` and
`ℓ ≠ p`, the absolute Galois group carries such a datum with inertia `I_k`, the coset of
geometric Frobenius lifts, and as tame character the `ℓ`-adic tame character
`TauCeti.inertiaPadicTameCharacter`, valued in `ℤ_ℓ(1)`, composed with a choice of
trivialization `ℤ_ℓ(1) ≅ ℤ_ℓ`. That choice is determined only up to a unit of `ℤ_ℓ`, which is
why isomorphisms of local monodromy data carry a constant.

Since the tame character is invariant under conjugation by inertia, the twist holds on the whole
Frobenius coset as soon as it holds at one Frobenius lift
(`MonoidHom.map_conjNormal_eq_of_inv_mul_mem`).
-/
structure LocalMonodromyDatum (ℓ : ℕ) [Fact ℓ.Prime] (H : Type u) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] where
  /-- The inertia subgroup. -/
  inertia : Subgroup H
  isClosed_inertia : IsClosed (inertia : Set H)
  [normal_inertia : inertia.Normal]
  /-- The tame character `inertia → ℚ_ℓ`, written multiplicatively. -/
  tame : inertia →ₜ* Multiplicative ℚ_[ℓ]
  tame_ne_one : tame ≠ 1
  /-- The integer `q`, by which conjugation by Frobenius divides the tame character. -/
  q : ℕ
  two_le_q : 2 ≤ q
  coprime_q : q.Coprime ℓ
  /-- The class of the Frobenius elements in `H ⧸ inertia`. -/
  frobClass : H ⧸ inertia
  exists_continuousMulEquiv_zHat : ∃ e : H ⧸ inertia ≃ₜ* zHat.{u}, e frobClass = zHat.gen
  tame_conj : ∀ Φ : H, (Φ : H ⧸ inertia) = frobClass → ∀ σ : inertia,
    (tame (MulAut.conjNormal Φ σ)).toAdd = (q : ℚ_[ℓ])⁻¹ * (tame σ).toAdd

namespace LocalMonodromyDatum

attribute [instance] normal_inertia

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H]
  {H' : Type v} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [CompactSpace H']
  [T2Space H'] [TotallyDisconnectedSpace H']
  {H'' : Type w} [Group H''] [TopologicalSpace H''] [IsTopologicalGroup H''] [CompactSpace H'']
  [T2Space H''] [TotallyDisconnectedSpace H'']

section Basic

variable (D : LocalMonodromyDatum ℓ H)

/-- Inertia is compact: Mathlib's instance for closed subgroups of a compact group. -/
instance compactSpace_inertia : CompactSpace D.inertia :=
  inferInstanceAs (CompactSpace (⟨D.inertia, D.isClosed_inertia⟩ : ClosedSubgroup H))

/-- Inertia is closed, as an instance: with it, `H ⧸ D.inertia` is again a profinite group. -/
instance : IsClosed (D.inertia : Set H) :=
  D.isClosed_inertia

/-- The **Frobenius coset** of a local monodromy datum: the elements of `H` whose class modulo
inertia is `frobClass`. -/
def frobenius : Set H :=
  {Φ | (Φ : H ⧸ D.inertia) = D.frobClass}

variable {D}

/-- Membership in the Frobenius coset. -/
@[simp]
theorem mem_frobenius {Φ : H} : Φ ∈ D.frobenius ↔ (Φ : H ⧸ D.inertia) = D.frobClass :=
  Iff.rfl

variable (D) in
/-- The Frobenius coset is nonempty. -/
theorem frobenius_nonempty : D.frobenius.Nonempty :=
  ⟨D.frobClass.out, QuotientGroup.out_eq' _⟩

/-- Two Frobenius elements differ by an element of inertia. -/
theorem inv_mul_mem_inertia {Φ Φ' : H} (hΦ : Φ ∈ D.frobenius) (hΦ' : Φ' ∈ D.frobenius) :
    Φ⁻¹ * Φ' ∈ D.inertia :=
  QuotientGroup.eq.1 (hΦ.trans hΦ'.symm)

/-- The Frobenius coset is the left coset of inertia through any of its elements. -/
theorem mem_frobenius_iff_inv_mul_mem {Φ Φ' : H} (hΦ : Φ ∈ D.frobenius) :
    Φ' ∈ D.frobenius ↔ Φ⁻¹ * Φ' ∈ D.inertia := by
  rw [mem_frobenius, ← hΦ, eq_comm, QuotientGroup.eq]

/-- A Frobenius element times an element of inertia is a Frobenius element. -/
theorem mul_mem_frobenius_right {Φ σ : H} (hΦ : Φ ∈ D.frobenius) (hσ : σ ∈ D.inertia) :
    Φ * σ ∈ D.frobenius := by
  rwa [mem_frobenius_iff_inv_mul_mem hΦ, inv_mul_cancel_left]

/-- An element of inertia times a Frobenius element is a Frobenius element. -/
theorem mul_mem_frobenius_left {σ Φ : H} (hσ : σ ∈ D.inertia) (hΦ : Φ ∈ D.frobenius) :
    σ * Φ ∈ D.frobenius := by
  rw [mem_frobenius, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff σ).2 hσ, one_mul]
  exact hΦ

/-- An element lies in the class `frobClass ^ n` exactly when it differs from the `n`-th power of
a Frobenius element by an element of inertia. -/
theorem coe_eq_frobClass_pow_iff {Φ : H} (hΦ : Φ ∈ D.frobenius) (x : H) (n : ℕ) :
    (x : H ⧸ D.inertia) = D.frobClass ^ n ↔ (Φ ^ n)⁻¹ * x ∈ D.inertia := by
  rw [← mem_frobenius.1 hΦ, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]

/-- The integer `q` is a unit in `ℚ_ℓ`. -/
theorem q_ne_zero : (D.q : ℚ_[ℓ]) ≠ 0 :=
  Nat.cast_ne_zero.2 (by have := D.two_le_q; lia)

/-- The integer `q` is different from `1` in `ℚ_ℓ`. -/
theorem q_ne_one : (D.q : ℚ_[ℓ]) ≠ 1 :=
  Nat.cast_ne_one.2 (by have := D.two_le_q; lia)

variable (D) in
/-- The tame character takes a nonzero value, in additive form. -/
theorem exists_toAdd_tame_ne_zero : ∃ σ, (D.tame σ).toAdd ≠ 0 := by
  obtain ⟨σ, hσ⟩ := DFunLike.ne_iff.1 D.tame_ne_one
  exact ⟨σ, fun h ↦ hσ (Multiplicative.toAdd.injective h)⟩

/-- The tame character is not identically zero on any open subgroup of inertia. -/
theorem exists_tame_ne_one_of_isOpen (U : Subgroup D.inertia) (hU : IsOpen (U : Set D.inertia)) :
    ∃ σ ∈ U, D.tame σ ≠ 1 := by
  -- `U` has finite index in the compact group `I`, so it contains a positive power `σ ^ n` of an
  -- element with `t(σ) ≠ 0`, and `t(σ ^ n) = n t(σ) ≠ 0` in characteristic zero.
  obtain ⟨σ, hσ⟩ := D.exists_toAdd_tame_ne_zero
  have : Finite (D.inertia ⧸ U) := U.quotient_finite_of_isOpen hU
  obtain ⟨n, hn, -, hσn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero U.index_ne_zero_of_finite σ
  refine ⟨σ ^ n, hσn, fun h ↦ hσ ?_⟩
  replace h := congrArg Multiplicative.toAdd h
  rw [map_pow, toAdd_pow, toAdd_one, nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn.ne')

/-- **Conjugation by an element of the class `frobClass ^ n` divides the tame character by
`q ^ n`**: `t(Φ σ Φ⁻¹) = q⁻ⁿ t(σ)`. -/
theorem tame_conj_of_coe_eq_frobClass_pow {Φ : H} {n : ℕ}
    (hΦ : (Φ : H ⧸ D.inertia) = D.frobClass ^ n) (σ : D.inertia) :
    (D.tame (MulAut.conjNormal Φ σ)).toAdd = ((D.q : ℚ_[ℓ]) ^ n)⁻¹ * (D.tame σ).toAdd := by
  -- Replace `Φ` by the power `Φ₀ ^ n` of a Frobenius element, then induct on `n`.
  obtain ⟨Φ₀, hΦ₀⟩ := D.frobenius_nonempty
  have h : D.tame (MulAut.conjNormal Φ σ) = D.tame (MulAut.conjNormal (Φ₀ ^ n) σ) :=
    D.tame.toMonoidHom.map_conjNormal_eq_of_inv_mul_mem ((coe_eq_frobClass_pow_iff hΦ₀ Φ n).1 hΦ) σ
  rw [h]
  clear h hΦ
  induction n generalizing σ with
  | zero => rw [pow_zero, map_one, MulAut.one_apply, pow_zero, inv_one, one_mul]
  | succ n ih =>
    rw [pow_succ', map_mul, MulAut.mul_apply, D.tame_conj Φ₀ hΦ₀, ih, pow_succ', mul_inv,
      mul_assoc]

/-- **`1` is not a Frobenius element.** -/
theorem one_notMem_frobenius : (1 : H) ∉ D.frobenius := by
  -- The twist at `Φ = 1` gives `(1 - q⁻¹) t(σ) = 0`, and `q ≠ 1`.
  intro h
  obtain ⟨σ, hσ⟩ := D.exists_toAdd_tame_ne_zero
  have hσ' := D.tame_conj 1 h σ
  rw [map_one, MulAut.one_apply, ← sub_eq_zero, ← one_sub_mul] at hσ'
  exact hσ ((mul_eq_zero.1 hσ').resolve_left (sub_ne_zero.2 (inv_ne_one.2 D.q_ne_one).symm))

/-- The Frobenius class is not trivial in `H ⧸ inertia`. -/
theorem frobClass_ne_one : D.frobClass ≠ 1 := fun h ↦
  D.one_notMem_frobenius (by rw [mem_frobenius, QuotientGroup.mk_one, h])

/-- The Frobenius coset is disjoint from inertia. -/
theorem disjoint_frobenius_inertia : Disjoint D.frobenius (D.inertia : Set H) :=
  Set.disjoint_left.2 fun Φ hΦ hI ↦ D.frobClass_ne_one <| by
    rw [← mem_frobenius.1 hΦ, (QuotientGroup.eq_one_iff Φ).2 hI]

/-- **The Frobenius class topologically generates `H ⧸ inertia`**: its integer powers are
dense. -/
theorem denseRange_zpow_frobClass : DenseRange fun n : ℤ ↦ D.frobClass ^ n := by
  obtain ⟨e, he⟩ := D.exists_continuousMulEquiv_zHat
  convert e.symm.surjective.denseRange.comp zHat.denseRange_zpow_gen e.symm.continuous
    using 2 with n
  simp [← he]

end Basic

section Ext

/-- Two local monodromy data agree when they have the same inertia, tame character, Frobenius
coset and `q`. -/
@[ext]
theorem ext {D D' : LocalMonodromyDatum ℓ H} (h_inertia : D.inertia = D'.inertia)
    (h_tame : ∀ σ (hσ : σ ∈ D.inertia) (hσ' : σ ∈ D'.inertia), D.tame ⟨σ, hσ⟩ = D'.tame ⟨σ, hσ'⟩)
    (h_frobenius : D.frobenius = D'.frobenius) (h_q : D.q = D'.q) : D = D' := by
  obtain ⟨I, hI, t, ht, q, hq, hqℓ, F, hF, htF⟩ := D
  obtain ⟨I', hI', t', ht', q', hq', hqℓ', F', hF', htF'⟩ := D'
  dsimp only at h_inertia h_q
  subst h_inertia h_q
  have htt' : t = t' := ContinuousMonoidHom.ext fun σ ↦ h_tame σ σ.property σ.property
  have hFF' : F = F' := by
    have h : F.out ∈ frobenius ⟨I, hI, t, ht, q, hq, hqℓ, F, hF, htF⟩ := QuotientGroup.out_eq' F
    rw [h_frobenius] at h
    exact (QuotientGroup.out_eq' F).symm.trans h
  subst htt' hFF'
  rfl

end Ext

section Smul

/-- Rescaling the tame character of a local monodromy datum by `c ∈ ℚ_ℓˣ`: the datum `c • D` has
the same inertia, Frobenius coset and `q`, and tame character `c t`. -/
instance : SMul ℚ_[ℓ]ˣ (LocalMonodromyDatum ℓ H) where
  smul c D :=
    { inertia := D.inertia
      isClosed_inertia := D.isClosed_inertia
      tame :=
        { toMonoidHom := (AddMonoidHom.mulLeft (c : ℚ_[ℓ])).toMultiplicative.comp D.tame
          continuous_toFun := continuous_ofAdd.comp
            (continuous_const.mul (continuous_toAdd.comp D.tame.continuous)) }
      tame_ne_one := fun h ↦
        have ⟨σ, hσ⟩ := D.exists_toAdd_tame_ne_zero
        mul_ne_zero c.ne_zero hσ (congrArg Multiplicative.toAdd (DFunLike.congr_fun h σ))
      q := D.q
      two_le_q := D.two_le_q
      coprime_q := D.coprime_q
      frobClass := D.frobClass
      exists_continuousMulEquiv_zHat := D.exists_continuousMulEquiv_zHat
      tame_conj := fun Φ hΦ σ ↦
        (congrArg ((c : ℚ_[ℓ]) * ·) (D.tame_conj Φ hΦ σ)).trans (mul_left_comm _ _ _) }

variable (c c' : ℚ_[ℓ]ˣ) (D : LocalMonodromyDatum ℓ H)

/-- Rescaling does not change inertia. -/
@[simp]
theorem smul_inertia : (c • D).inertia = D.inertia :=
  (rfl)

/-- The tame character of `c • D` is `c` times that of `D`. -/
@[simp]
theorem toAdd_smul_tame (σ : D.inertia) : ((c • D).tame σ).toAdd = c * (D.tame σ).toAdd :=
  (rfl)

/-- Rescaling does not change `q`. -/
@[simp]
theorem smul_q : (c • D).q = D.q :=
  (rfl)

/-- Rescaling does not change the Frobenius class. -/
@[simp]
theorem smul_frobClass : (c • D).frobClass = D.frobClass :=
  (rfl)

/-- Rescaling does not change the Frobenius coset. -/
@[simp]
theorem smul_frobenius : (c • D).frobenius = D.frobenius :=
  (rfl)

/-- Rescaling the tame character is an action of `ℚ_ℓˣ` on local monodromy data. -/
instance : MulAction ℚ_[ℓ]ˣ (LocalMonodromyDatum ℓ H) where
  one_smul D := LocalMonodromyDatum.ext rfl
    (fun σ hσ _ ↦ Multiplicative.toAdd.injective <| by
      rw [toAdd_smul_tame, Units.val_one, one_mul]) (smul_frobenius _ _) rfl
  mul_smul c c' D := LocalMonodromyDatum.ext rfl
    (fun σ hσ _ ↦ Multiplicative.toAdd.injective <| by
      rw [toAdd_smul_tame, toAdd_smul_tame, toAdd_smul_tame, Units.val_mul, mul_assoc])
    (by rw [smul_frobenius, smul_frobenius, smul_frobenius]) rfl

end Smul

section IsIso

/-- `α : H ≃ₜ* H'` is an **isomorphism of local monodromy data** `D → D'` with constant
`c ∈ ℚ_ℓˣ`: it carries inertia onto inertia and the Frobenius coset onto the Frobenius coset, the
two data have the same `q`, and `t' ∘ α = c t` on inertia. -/
structure IsIso (D : LocalMonodromyDatum ℓ H) (D' : LocalMonodromyDatum ℓ H') (α : H ≃ₜ* H')
    (c : ℚ_[ℓ]ˣ) : Prop where
  map_mem_inertia_iff (σ : H) : α σ ∈ D'.inertia ↔ σ ∈ D.inertia
  map_mem_frobenius_iff (Φ : H) : α Φ ∈ D'.frobenius ↔ Φ ∈ D.frobenius
  q_eq : D.q = D'.q
  toAdd_tame_map (σ : H) (hσ : σ ∈ D.inertia) (hσ' : α σ ∈ D'.inertia) :
    (D'.tame ⟨α σ, hσ'⟩).toAdd = c * (D.tame ⟨σ, hσ⟩).toAdd

variable {D : LocalMonodromyDatum ℓ H} {D' : LocalMonodromyDatum ℓ H'}
  {D'' : LocalMonodromyDatum ℓ H''} {α : H ≃ₜ* H'} {β : H' ≃ₜ* H''} {c c' : ℚ_[ℓ]ˣ}

namespace IsIso

/-- An isomorphism of local monodromy data maps inertia onto inertia. -/
theorem map_inertia (h : IsIso D D' α c) : D.inertia.map (α : H →* H') = D'.inertia := by
  ext σ'
  refine ⟨?_, fun hσ' ↦ ⟨α.symm σ', ?_, by simp⟩⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (h.map_mem_inertia_iff σ).2 hσ
  · exact (h.map_mem_inertia_iff _).1 (by rwa [α.apply_symm_apply])

/-- An isomorphism of local monodromy data maps the Frobenius coset onto the Frobenius coset. -/
theorem image_frobenius (h : IsIso D D' α c) : α '' D.frobenius = D'.frobenius := by
  ext Φ'
  rw [← α.apply_symm_apply Φ', α.injective.mem_set_image, h.map_mem_frobenius_iff]

variable (D) in
/-- The identity is an isomorphism `D → D` with constant `1`. -/
theorem refl : IsIso D D (ContinuousMulEquiv.refl H) 1 where
  map_mem_inertia_iff _ := Iff.rfl
  map_mem_frobenius_iff _ := Iff.rfl
  q_eq := rfl
  toAdd_tame_map _ _ _ := by simp only [ContinuousMulEquiv.refl_apply, Units.val_one, one_mul]

/-- The inverse of an isomorphism `D → D'` with constant `c` is an isomorphism `D' → D` with
constant `c⁻¹`. -/
theorem symm (h : IsIso D D' α c) : IsIso D' D α.symm c⁻¹ where
  map_mem_inertia_iff σ' := by rw [← h.map_mem_inertia_iff, α.apply_symm_apply]
  map_mem_frobenius_iff Φ' := by rw [← h.map_mem_frobenius_iff, α.apply_symm_apply]
  q_eq := h.q_eq.symm
  toAdd_tame_map σ' hσ' hσ := by
    have h' := h.toAdd_tame_map (α.symm σ') hσ ((h.map_mem_inertia_iff _).2 hσ)
    simp only [α.apply_symm_apply] at h'
    rw [h', Units.inv_mul_cancel_left]

/-- The composite of isomorphisms `D → D'` and `D' → D''` with constants `c` and `c'` is an
isomorphism `D → D''` with constant `c' * c`. -/
theorem trans (h : IsIso D D' α c) (h' : IsIso D' D'' β c') :
    IsIso D D'' (α.trans β) (c' * c) where
  map_mem_inertia_iff σ := (h'.map_mem_inertia_iff (α σ)).trans (h.map_mem_inertia_iff σ)
  map_mem_frobenius_iff Φ := (h'.map_mem_frobenius_iff (α Φ)).trans (h.map_mem_frobenius_iff Φ)
  q_eq := h.q_eq.trans h'.q_eq
  toAdd_tame_map σ hσ hσ'' := by
    have hσ' := (h.map_mem_inertia_iff σ).2 hσ
    simp only [ContinuousMulEquiv.trans_apply]
    rw [h'.toAdd_tame_map _ hσ', h.toAdd_tame_map σ hσ hσ', Units.val_mul, mul_assoc]

/-- An isomorphism of local monodromy data preserves the classes of the powers of Frobenius:
`α x` lies in `frobClass' ^ n` exactly when `x` lies in `frobClass ^ n`. -/
theorem coe_apply_eq_frobClass_pow_iff (h : IsIso D D' α c) (x : H) (n : ℕ) :
    (α x : H' ⧸ D'.inertia) = D'.frobClass ^ n ↔ (x : H ⧸ D.inertia) = D.frobClass ^ n := by
  obtain ⟨Φ, hΦ⟩ := D.frobenius_nonempty
  rw [coe_eq_frobClass_pow_iff ((h.map_mem_frobenius_iff Φ).2 hΦ), coe_eq_frobClass_pow_iff hΦ,
    ← map_pow, ← map_inv, ← map_mul, h.map_mem_inertia_iff]

/-- The constant of an isomorphism of local monodromy data is determined by the underlying group
isomorphism. -/
theorem const_eq (h : IsIso D D' α c) (h' : IsIso D D' α c') : c = c' := by
  obtain ⟨σ, hσ⟩ := D.exists_toAdd_tame_ne_zero
  have hσ' := (h.map_mem_inertia_iff σ).2 σ.property
  exact Units.ext <| mul_right_cancel₀ hσ <|
    (h.toAdd_tame_map σ σ.property hσ').symm.trans (h'.toAdd_tame_map σ σ.property hσ')

variable (c') in
/-- An isomorphism `D → D'` with constant `c` is an isomorphism `D → c' • D'` with constant
`c' * c`. -/
theorem smul_right (h : IsIso D D' α c) : IsIso D (c' • D') α (c' * c) where
  map_mem_inertia_iff := h.map_mem_inertia_iff
  map_mem_frobenius_iff := h.map_mem_frobenius_iff
  q_eq := h.q_eq
  toAdd_tame_map σ hσ hσ' := by
    rw [toAdd_smul_tame, h.toAdd_tame_map σ hσ hσ', Units.val_mul, mul_assoc]

variable (c') in
/-- An isomorphism `D → D'` with constant `c` is an isomorphism `c' • D → D'` with constant
`c * c'⁻¹`. -/
theorem smul_left (h : IsIso D D' α c) : IsIso (c' • D) D' α (c * c'⁻¹) where
  map_mem_inertia_iff := h.map_mem_inertia_iff
  map_mem_frobenius_iff := h.map_mem_frobenius_iff
  q_eq := h.q_eq
  toAdd_tame_map σ hσ hσ' := by
    rw [toAdd_smul_tame, h.toAdd_tame_map σ hσ hσ', Units.val_mul, mul_assoc,
      Units.inv_mul_cancel_left]

end IsIso

variable (c : ℚ_[ℓ]ˣ) (D : LocalMonodromyDatum ℓ H)

/-- The identity is an isomorphism `D → c • D` with constant `c`. -/
theorem isIso_refl_smul : IsIso D (c • D) (ContinuousMulEquiv.refl H) c where
  map_mem_inertia_iff _ := Iff.rfl
  map_mem_frobenius_iff _ := Iff.rfl
  q_eq := rfl
  toAdd_tame_map _ _ _ := by simp only [ContinuousMulEquiv.refl_apply, toAdd_smul_tame]

/-- The identity is an isomorphism `c • D → D` with constant `c⁻¹`. -/
theorem isIso_smul_refl : IsIso (c • D) D (ContinuousMulEquiv.refl H) c⁻¹ where
  map_mem_inertia_iff _ := Iff.rfl
  map_mem_frobenius_iff _ := Iff.rfl
  q_eq := rfl
  toAdd_tame_map _ _ _ := by
    simp only [ContinuousMulEquiv.refl_apply]
    rw [toAdd_smul_tame, Units.inv_mul_cancel_left]

/-- The identity is an isomorphism `D → c • D` with constant `c'` exactly when `c' = c`; for
instance, it is not an isomorphism `D → ℓ • D` with constant `1`. -/
theorem isIso_refl_smul_iff : IsIso D (c • D) (ContinuousMulEquiv.refl H) c' ↔ c' = c :=
  ⟨fun h ↦ h.const_eq (isIso_refl_smul c D), fun h ↦ h ▸ isIso_refl_smul c D⟩

end IsIso

end LocalMonodromyDatum

end TauCeti
