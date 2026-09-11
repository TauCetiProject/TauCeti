/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The descent matrices at a prime

Miyake's level descent at a prime `p` runs over the `p` upper-triangular matrices `[1, v; 0, p]`
together with, when `p` divides `N` but `p²` does not, one further matrix built from an element
of `Γ₀(N / p)` reducing to `S = [[0, -1], [1, 0]]` modulo `p` and to the identity modulo `N / p`.
This file supplies that extra matrix, assembles the family of `p` or `p + 1` elements of `GL₂(ℝ)`
the descent runs over, and computes their determinants.

The extra matrix comes from strong approximation at a coprime pair of levels,
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq`: for coprime `d` and `d'` the principal
congruence subgroup `Γ(d')` still surjects onto `SL₂(ℤ/dℤ)`. The descent is that statement at
`d = p` and `d' = N / p` — a coprime pair exactly because `p` divides `N` while `p²` does not —
with `S` as the prescribed reduction modulo `p`. Approximation returns membership in `Γ(N / p)`,
which is stronger than the `Γ₀(N / p)` the descent asks for, so the second reduction is the
identity rather than merely lower-triangular.

## Main definitions

* `TauCeti.descendMatrixCount`: the size of the family, `p` when `p² ∣ N` and `p + 1` otherwise.
* `TauCeti.descendExtraGamma`: the extra matrix, with the junk value `1` outside the hypotheses
  that make the choice.
* `TauCeti.descendMatrixRat`: the family before the embedding into `GL₂(ℝ)`, indexed by
  `Fin (descendMatrixCount p N)`.
* `TauCeti.descendMatrix`: the family itself, the image of `descendMatrixRat` in `GL₂(ℝ)`
  (`descendMatrix_eq_map`); `descendMatrixRat_of_lt`/`descendMatrixRat_of_le` and
  `descendMatrix_of_lt`/`descendMatrix_of_le` describe the members, and `descendMatrixRat_det`/
  `descendMatrix_det` their determinant.

## Main results

* `TauCeti.exists_mem_Gamma0_map_intCast_zmod_eq_S`: for a prime `p` with `p ∣ N` and `p² ∤ N`,
  some `γ ∈ Γ₀(N / p)` reduces to `S` modulo `p` and to the identity modulo `N / p`.
* `TauCeti.descendExtraGamma_mem_Gamma0`, `TauCeti.descendExtraGamma_map_intCast_zmod_eq_S` and
  `TauCeti.descendExtraGamma_map_intCast_zmod_div_eq_one`: those three properties, read back off
  the chosen matrix.
* `TauCeti.descendExtraGamma_eq_one_of_not`: outside the hypotheses that make the choice, the
  extra matrix is the identity.
* `TauCeti.descendMatrixCount_of_sq_dvd` and `TauCeti.descendMatrixCount_of_not_sq_dvd`: the two
  values of the count.
* `TauCeti.descendMatrix_of_lt` and `TauCeti.descendMatrix_of_le`: the two branches of the
  family, as equations in `GL₂(ℝ)`.
* `TauCeti.descendMatrix_det`: every member of the family has determinant `p`.
* `TauCeti.descendMatrix_det_pos`: that determinant is positive, which is what the slash action
  needs to pull a scalar through a member of the family.

## Scope

The family is defined and its determinants computed. That its members *are* a set of coset
representatives, and that the associated slash sum descends the level, are separate statements
about the double coset `Γ₀(N) diag(1, p) Γ₀(N)`; neither is proved here. Until they are, the
family is the intended list of representatives rather than a formalized one.

Follows the AINTLIB `LeanModularForms` project, whose `descendExtraGamma`, `descendCosetCount`,
`descendCosetList` and `descendCosetList_det` are the counterparts of the declarations here — the
names differ because nothing here proves these matrices are coset representatives — and
specializes its `descendExtraGamma_exists`
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which proves the
same existence directly; here it is read off the general coprime-level statement instead.
-/

public section

open CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups

namespace TauCeti

/-- **A matrix with prescribed reductions at `p` and at `N / p`.** For a prime `p` with `p ∣ N` but
`p² ∤ N`, there is a `γ ∈ Γ₀(N / p)` reducing to `S = [[0, -1], [1, 0]]` modulo `p` and to the
identity modulo `N / p`.

`p² ∤ N` is exactly what makes `p` coprime to `N / p`; the target modulo `p` is `S`, and membership
in `Γ₀(N / p)` comes from the stronger `Γ(N / p)` that
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq` already delivers.

This is the matrix Miyake's Lemma 4.5.11 takes as its extra coset representative for the level
descent when `p` exactly divides `N`. Only existence and the two reductions are proved here: the
coset system is not formalized, so nothing is claimed about enumerating or completing it. -/
theorem exists_mem_Gamma0_map_intCast_zmod_eq_S {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    ∃ γ ∈ Gamma0 (N / p),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ =
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) γ = 1 := by
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h ↦ hpsq <| by
    have hmul := Nat.mul_dvd_mul_left p h
    rwa [Nat.mul_div_cancel' hpN, ← sq] at hmul
  obtain ⟨γ, hγ, hγp⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S)
  exact ⟨γ, Gamma_le_Gamma0 _ hγ, hγp, Gamma_mem'.mp hγ⟩

/-- **The size of the descent family at `p`.** Miyake's count: `p` when `p²` divides `N`, and
`p + 1` when it does not, the extra member being the one `descendExtraGamma` supplies. -/
def descendMatrixCount (p N : ℕ) : ℕ := if p ^ 2 ∣ N then p else p + 1

/-- The descent family has `p` members when `p²` divides `N`. -/
@[simp]
theorem descendMatrixCount_of_sq_dvd {p N : ℕ} (h : p ^ 2 ∣ N) : descendMatrixCount p N = p := by
  simp [descendMatrixCount, h]

/-- The descent family has `p + 1` members when `p²` does not divide `N`. -/
@[simp]
theorem descendMatrixCount_of_not_sq_dvd {p N : ℕ} (h : ¬ p ^ 2 ∣ N) :
    descendMatrixCount p N = p + 1 := by
  simp [descendMatrixCount, h]

/-- **The extra descent matrix.** For a prime `p` exactly dividing `N`, an element of `Γ₀(N / p)`
reducing to `S` modulo `p` and to the identity modulo `N / p`; the junk value `1` when those
hypotheses fail, so that the definition is total. Its three defining properties are
`descendExtraGamma_mem_Gamma0`, `descendExtraGamma_map_intCast_zmod_eq_S` and
`descendExtraGamma_map_intCast_zmod_div_eq_one`. -/
noncomputable def descendExtraGamma (p N : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N then
    (exists_mem_Gamma0_map_intCast_zmod_eq_S h.1 h.2.1 h.2.2).choose
  else 1

/-- Under the hypotheses that make the choice, `descendExtraGamma` *is* the chosen matrix. -/
private theorem descendExtraGamma_eq_choose {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    descendExtraGamma p N = (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose :=
  -- `dif_pos` is deprecated on the current pin, so the guard is discharged the way
  -- `TauCeti.diamondOpNat_of_coprime` does it
  dite_eq_left_of_eq_true (by simp [hp, hpN, hpsq])

/-- **The extra descent matrix lies in `Γ₀(N / p)`.** -/
theorem descendExtraGamma_mem_Gamma0 {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) : descendExtraGamma p N ∈ Gamma0 (N / p) := by
  rw [descendExtraGamma_eq_choose hp hpN hpsq]
  exact (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose_spec.1

/-- **The extra descent matrix reduces to `S` modulo `p`.** -/
@[simp]
theorem descendExtraGamma_map_intCast_zmod_eq_S {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (descendExtraGamma p N) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S := by
  rw [descendExtraGamma_eq_choose hp hpN hpsq]
  exact (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose_spec.2.1

/-- **The extra descent matrix reduces to the identity modulo `N / p`.** -/
@[simp]
theorem descendExtraGamma_map_intCast_zmod_div_eq_one {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) (descendExtraGamma p N) = 1 := by
  rw [descendExtraGamma_eq_choose hp hpN hpsq]
  exact (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose_spec.2.2

/-- **Outside its guard the extra matrix is the identity.** For `p` not prime, or not dividing
`N`, or with `p²` dividing `N`, the choice is not available and `descendExtraGamma` takes its
junk value. -/
@[simp]
theorem descendExtraGamma_eq_one_of_not {p N : ℕ} (h : ¬ (p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N)) :
    descendExtraGamma p N = 1 := by
  simp [descendExtraGamma, h]

/-- **The descent family at `p`, over `ℚ`** (Miyake, Lemma 4.5.11): a family in `GL₂(ℚ)` made of
the `p` upper-triangular matrices `upperTriRep p v = [1, v; 0, p]` for `v < p` — this
repository's `T_p` representative family — together with, when `p²` does not divide `N`, so
that `descendMatrixCount` is `p + 1`, the further matrix `[1, 0; 0, p] * mapGL ℚ γ_p`, where
`γ_p = descendExtraGamma p N` is embedded into `GL₂(ℚ)` by `mapGL ℚ`.

Neither `p ∣ N` nor primality of `p` is required: the construction uses only `p ≠ 0`, to name the
zero index of `Fin p`. Those two hypotheses are what make the family the *descent* family at a
prime — without `p ∣ N` the matrix `descendExtraGamma p N` is `1` and the extra member degenerates
to `[1, 0; 0, p]`, which the first branch already lists at `v = 0` — so they belong on the later
results that establish descent, not on the family itself. -/
noncomputable def descendMatrixRat (p N : ℕ) [NeZero p] :
    Fin (descendMatrixCount p N) → GL (Fin 2) ℚ := fun v ↦
  if h : v.val < p then upperTriRep p ⟨v.val, h⟩
  else upperTriRep p ⟨0, NeZero.pos p⟩ * Matrix.SpecialLinearGroup.mapGL ℚ (descendExtraGamma p N)

/-- **The descent family**, the image of `descendMatrixRat p N` in `GL₂(ℝ)`, where the slash
action of a modular form lives. -/
noncomputable def descendMatrix (p N : ℕ) [NeZero p] :
    Fin (descendMatrixCount p N) → GL (Fin 2) ℝ := fun v ↦
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (descendMatrixRat p N v)

/-- The descent family is the image of the rational descent family. -/
theorem descendMatrix_eq_map (p N : ℕ) [NeZero p] (v : Fin (descendMatrixCount p N)) :
    descendMatrix p N v = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (descendMatrixRat p N v) :=
  (rfl)

/-- The members of the rational descent family below index `p` are the upper-triangular
matrices `[1, v; 0, p]`. -/
@[simp]
theorem descendMatrixRat_of_lt {p N : ℕ} [NeZero p]
    {v : Fin (descendMatrixCount p N)} (h : v.val < p) :
    descendMatrixRat p N v = upperTriRep p ⟨v.val, h⟩ := by
  rw [descendMatrixRat]
  split_ifs
  rfl

/-- The member of the rational descent family at index `p`, present exactly when `p²` does not
divide `N`, is `[1, 0; 0, p]` times the extra matrix. -/
@[simp]
theorem descendMatrixRat_of_le {p N : ℕ} [NeZero p]
    {v : Fin (descendMatrixCount p N)} (h : p ≤ v.val) :
    descendMatrixRat p N v = upperTriRep p ⟨0, NeZero.pos p⟩ *
      Matrix.SpecialLinearGroup.mapGL ℚ (descendExtraGamma p N) := by
  rw [descendMatrixRat]
  split_ifs with h'
  · exact absurd h' (Nat.not_lt.mpr h)
  · rfl

/-- The members of the descent family below index `p` are the upper-triangular matrices
`[1, v; 0, p]`. -/
@[simp]
theorem descendMatrix_of_lt {p N : ℕ} [NeZero p]
    {v : Fin (descendMatrixCount p N)} (h : v.val < p) :
    descendMatrix p N v =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨v.val, h⟩) := by
  rw [descendMatrix_eq_map, descendMatrixRat_of_lt h]

/-- The member of the descent family at index `p`, present exactly when `p²` does not divide `N`,
is `[1, 0; 0, p]` times the extra matrix. -/
@[simp]
theorem descendMatrix_of_le {p N : ℕ} [NeZero p]
    {v : Fin (descendMatrixCount p N)} (h : p ≤ v.val) :
    descendMatrix p N v =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        Matrix.SpecialLinearGroup.mapGL ℝ (descendExtraGamma p N) := by
  rw [descendMatrix_eq_map, descendMatrixRat_of_le h, map_mul, Matrix.SpecialLinearGroup.map_mapGL]

/-- **Every member of the rational descent family has determinant `p`.** Every element of the
double coset `Γ₀(N) diag(1, p) Γ₀(N)` that the descent sum runs over has determinant `p`, so this
is a necessary condition for lying in it, not a characterisation of it; that these matrices lie
in the double coset is not proved here. -/
@[simp]
theorem descendMatrixRat_det (p N : ℕ) [NeZero p] (v : Fin (descendMatrixCount p N)) :
    (descendMatrixRat p N v : Matrix (Fin 2) (Fin 2) ℚ).det = (p : ℚ) := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℚ (descendExtraGamma p N) :
      Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  rw [descendMatrixRat]
  split_ifs
  · simp [Matrix.det_fin_two]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hγ, mul_one]
    simp [Matrix.det_fin_two]

/-- **Every member of the descent family has determinant `p`**: the image under `algebraMap ℚ ℝ`
of `descendMatrixRat_det`. -/
@[simp]
theorem descendMatrix_det (p N : ℕ) [NeZero p]
    (v : Fin (descendMatrixCount p N)) :
    (descendMatrix p N v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
  rw [descendMatrix_eq_map, Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, descendMatrixRat_det, map_natCast]

/-- Every member of the descent family has positive determinant, namely `p`. -/
theorem descendMatrix_det_pos (p N : ℕ) [NeZero p] (v : Fin (descendMatrixCount p N)) :
    0 < (descendMatrix p N v : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [descendMatrix_det]
  exact_mod_cast NeZero.pos p

end TauCeti
