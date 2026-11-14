/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicAut
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.Data.Sum.Basic
import TauCeti.Data.List.ProdOfFn
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# The basic sequence of automorphisms of an orientable quadratic equation

For pairwise distinct variables `xᵢ`, `yᵢ` (`i = 1, …, n`) and `zⱼ` (`j = 1, …, m`) and
coefficients `cⱼ ∈ G`, the basic sequence `Γ = (γ₁, …, γ_K)` of [IFT], §7.1, lists the basic
automorphisms of `G[X]` fixing the word `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]`: first the
automorphisms of the adjacent coefficient atoms, then the automorphism of the last coefficient
atom and the first commutator, then for each commutator the automorphisms `yᵢ ↦ xᵢ yᵢ`,
`xᵢ ↦ yᵢ xᵢ`, `yᵢ ↦ xᵢ yᵢ` and the automorphism of this commutator and the next one. It has
`K(m, n)` terms, where `K(m, n) = m + 4n - 1` for `m, n ≠ 0`, `K(0, n) = 4n - 1` and
`K(m, 0) = m - 1`. The automorphisms `φ_{j,p}` are the products of powers of the terms of the
sequence, continued periodically. Composing a solution of a quadratic equation with the
`φ_{j,p}` produces the families of solutions that are used to lift equations to the coordinate
group of the quadratic equation.

## Order of the atoms

[IFT], §7.1, writes a standard orientable quadratic equation with the coefficient atoms first,
`∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] d⁻¹ = 1`, whereas `TauCeti.GroupAlgGeom.Quadratic.Standard` follows
[IFT], §2.7, and puts the commutators first, `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`.

When there is no coefficient atom (`m = 0`) the two shapes coincide: the product of the atoms of
the equation is the word `S₀` of its own variables (`basicWord_eq_prod_atoms_orientable`,
`basicWord_eq_prod_atoms_orientableCoeff_zero`), and the basic sequence `basicSeq S` is the
sequence `basicWordSeq` of [IFT] in these variables, beginning with `y₁ ↦ x₁ y₁`.

When there are coefficient atoms (`m ≠ 0`) the two shapes are exchanged by inversion: the inverse
of `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ` is the word `S₀` for the mirrored variables and coefficients
`xᵢ' = y_{n+1-i}`, `yᵢ' = x_{n+1-i}`, `zⱼ' = z_{m+1-j}` and `cⱼ' = c_{m+1-j}⁻¹`
(`basicWord_rev_eq_inv_prod_atoms_orientableCoeff`), and `basicSeq S` is by definition the
sequence `basicWordSeq` of these mirrored data, so that the formulas of [IFT] apply verbatim to
`S₀`.

In both cases the automorphisms of `basicSeq S` fix the coefficients and the left side of `S`
(`apply_toWord_of_mem_basicSeq`).

## Order of composition

[IFT] writes automorphisms as exponents, so that in `φ_{j,p} = γ_j^{p_j} ⋯ γ₁^{p₁}` the
automorphism `γ_j^{p_j}` is applied first: `z^{φ_j} = (z^{γ_j^{p_j}})^{φ_{j-1}}` (see the proof of
[IFT], Lemma 44). In `MulAut (G[X])`, where `(f * g) w = f (g w)`, this is the product
`γ₁ ^ p₁ * ⋯ * γ_j ^ p_j`, which is how `phi` is defined.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.basicWordSeq`: the basic sequence of the word `S₀`.
* `TauCeti.GroupAlgGeom.Lift.basicSeq`: the basic sequence of a standard orientable quadratic
  equation.
* `TauCeti.GroupAlgGeom.Lift.phi`: the products `φ_{j,p}` of powers of the terms of a sequence,
  continued periodically.

## Main results

* `TauCeti.GroupAlgGeom.Lift.mem_basicWordSeq_iff`: the members of the basic sequence.
* `TauCeti.GroupAlgGeom.Lift.apply_basicWord_of_mem_basicWordSeq`: the automorphisms of the basic
  sequence fix `S₀`.
* `TauCeti.GroupAlgGeom.Lift.length_basicWordSeq`: the basic sequence has `K(m, n)` terms.
* `TauCeti.GroupAlgGeom.Lift.apply_toWord_of_mem_basicSeq`: the automorphisms of the basic
  sequence of a standard orientable quadratic equation fix its left side.
* `TauCeti.GroupAlgGeom.Lift.phi_basicSeq_toWord`: the automorphisms `φ_{j,p}` fix the left side
  of the equation.
* `TauCeti.GroupAlgGeom.Lift.wordMap_phi_basicSeq_mem_V_iff`: the automorphisms `φ_{j,p}` permute
  the solutions of the equation.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1, Lemma 41 and Notation 42.
* [LIFT] O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions
  into generic points*, Contemp. Math. 378 (2005), §4.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G X : Type*} [Group G] {n m : ℕ}

/-! ### The basic sequence -/

section Seq

variable {x y : Fin n → X} {z : Fin m → X} (inj : (Sum.elim (Sum.elim x y) z).Injective)
  (c : Fin m → G)

/-- The basic sequence `Γ = (γ₁, …, γ_K)` of automorphisms of `G[X]` fixing the word
`S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` ([IFT], §7.1): the automorphisms of the adjacent coefficient
atoms, then, if there are both coefficient atoms and commutators, the automorphism of the last
coefficient atom and the first commutator, then for each commutator the automorphisms
`y_i ↦ x_i y_i`, `x_i ↦ y_i x_i`, `y_i ↦ x_i y_i` followed, if it is not the last one, by the
automorphism of this commutator and the next one. -/
noncomputable def basicWordSeq : List (MulAut (GX G X)) :=
  (List.ofFn fun j : Fin (m - 1) => basicCoeff inj c ⟨j, by omega⟩ ⟨j + 1, by omega⟩) ++
    (if h : 0 < m ∧ 0 < n then [basicLink inj c ⟨m - 1, by omega⟩ ⟨0, h.2⟩] else []) ++
    (List.ofFn fun i : Fin n => [basicY inj i, basicX inj i, basicY inj i] ++
      if h : (i : ℕ) + 1 < n then [basicComm inj i ⟨i + 1, h⟩] else []).flatten

theorem basicWordSeq_def :
    basicWordSeq inj c =
      (List.ofFn fun j : Fin (m - 1) => basicCoeff inj c ⟨j, by omega⟩ ⟨j + 1, by omega⟩) ++
        (if h : 0 < m ∧ 0 < n then [basicLink inj c ⟨m - 1, by omega⟩ ⟨0, h.2⟩] else []) ++
        (List.ofFn fun i : Fin n => [basicY inj i, basicX inj i, basicY inj i] ++
          if h : (i : ℕ) + 1 < n then [basicComm inj i ⟨i + 1, h⟩] else []).flatten := (rfl)

/-- The basic sequence has `K(m, n)` terms: `m + 4n - 1` when `m, n ≠ 0`, `4n - 1` when `m = 0`
and `m - 1` when `n = 0`. -/
@[simp]
theorem length_basicWordSeq :
    (basicWordSeq inj c).length = (m - 1) + (if 0 < m ∧ 0 < n then 1 else 0) + (4 * n - 1) := by
  have h : ∀ k : ℕ, ∑ i : Fin k, (3 + if (i : ℕ) + 1 < k then 1 else 0) = 4 * k - 1 := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [Fin.sum_univ_castSucc]
      simp
      omega
  rw [basicWordSeq_def, List.length_append, List.length_append, List.length_ofFn,
    List.length_flatten, List.map_ofFn, List.sum_ofFn, ← h n]
  congr 2
  · split_ifs <;> rfl
  · funext i
    simp only [Function.comp_apply, List.length_append]
    split_ifs <;> rfl

/-- The members of the basic sequence: the automorphisms of adjacent coefficient atoms, the
automorphism of the last coefficient atom and the first commutator, the automorphisms
`y_i ↦ x_i y_i` and `x_i ↦ y_i x_i`, and the automorphisms of adjacent commutators. -/
theorem mem_basicWordSeq_iff {γ : MulAut (GX G X)} :
    γ ∈ basicWordSeq inj c ↔
      (∃ j j' : Fin m, (j : ℕ) + 1 = j' ∧ γ = basicCoeff inj c j j') ∨
        (∃ (j : Fin m) (i : Fin n), (j : ℕ) + 1 = m ∧ (i : ℕ) = 0 ∧ γ = basicLink inj c j i) ∨
        (∃ i, γ = basicY inj i) ∨ (∃ i, γ = basicX inj i) ∨
        ∃ i i' : Fin n, (i : ℕ) + 1 = i' ∧ γ = basicComm inj i i' := by
  refine ⟨fun hγ => ?_, ?_⟩
  · simp only [basicWordSeq_def, List.mem_append, List.mem_ofFn, List.mem_flatten] at hγ
    obtain (⟨j, rfl⟩ | hγ) | ⟨l, ⟨i, rfl⟩, hγ⟩ := hγ
    · exact .inl ⟨_, _, rfl, rfl⟩
    · split_ifs at hγ with h
      · exact .inr (.inl ⟨_, _, by simp; omega, rfl, List.mem_singleton.1 hγ⟩)
      · simp at hγ
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hγ
      obtain (rfl | rfl | rfl) | hγ := hγ
      · exact .inr (.inr (.inl ⟨i, rfl⟩))
      · exact .inr (.inr (.inr (.inl ⟨i, rfl⟩)))
      · exact .inr (.inr (.inl ⟨i, rfl⟩))
      · split_ifs at hγ with h
        · exact .inr (.inr (.inr (.inr ⟨_, _, rfl, List.mem_singleton.1 hγ⟩)))
        · simp at hγ
  · rintro (⟨j, j', h, rfl⟩ | ⟨j, i, hj, hi, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, i', h, rfl⟩)
    · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.2 ⟨⟨j, by omega⟩, ?_⟩))
      exact congrArg (basicCoeff inj c j) (Fin.ext h)
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [dite_eq_left ⟨by omega, i.pos⟩, List.mem_singleton]
      exact congrArg₂ (basicLink inj c) (Fin.ext (by simp; omega)) (Fin.ext hi)
    · exact List.mem_append_right _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, by simp⟩)
    · exact List.mem_append_right _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, by simp⟩)
    · refine List.mem_append_right _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, ?_⟩)
      rw [dite_eq_left (by omega : (i : ℕ) + 1 < n)]
      exact List.mem_append_right _ (List.mem_singleton.2 (congrArg _ (Fin.ext h.symm)))

/-- Every automorphism of the basic sequence fixes the word `S₀`. -/
theorem apply_basicWord_of_mem_basicWordSeq {γ : MulAut (GX G X)} (hγ : γ ∈ basicWordSeq inj c) :
    γ (basicWord x y z c) = basicWord x y z c := by
  obtain ⟨j, j', h, rfl⟩ | ⟨j, i, hj, hi, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, i', h, rfl⟩ :=
    (mem_basicWordSeq_iff inj c).1 hγ
  · exact basicCoeff_basicWord inj c j j' h
  · exact basicLink_basicWord inj c j i hj hi
  · exact basicY_basicWord inj c i
  · exact basicX_basicWord inj c i
  · exact basicComm_basicWord inj c i i' h

/-- Every automorphism of the basic sequence fixes the coefficients. -/
theorem apply_inl_of_mem_basicWordSeq {γ : MulAut (GX G X)} (hγ : γ ∈ basicWordSeq inj c)
    (g : G) : γ (inl g) = inl g := by
  obtain ⟨j, j', -, rfl⟩ | ⟨j, i, -, -, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, i', -, rfl⟩ :=
    (mem_basicWordSeq_iff inj c).1 hγ
  · exact basicCoeff_inl inj c j j' g
  · exact basicLink_inl inj c j i g
  · exact basicY_inl inj i g
  · exact basicX_inl inj i g
  · exact basicComm_inl inj i i' g

end Seq

/-! ### The products `φ_{j,p}` -/

section Phi

variable {M : Type*} [Monoid M]

/-- The product `φ_{j,p}` of [IFT], §7.1, for a sequence `Γ = (γ₁, …, γ_K)` of elements of a
monoid and a tuple `p = (p₁, …, p_j)` of exponents: the product `γ₁ ^ p₁ * ⋯ * γ_j ^ p_j`, where
the sequence is continued periodically, `γ_{i+K} = γ_i`. For a sequence of automorphisms, the
automorphism `γ_j ^ p_j` is applied first and `γ₁ ^ p₁` last. -/
def phi (Γ : List M) (p : List ℕ) : M :=
  (p.zipIdx.map fun ei => Γ.getD (ei.2 % Γ.length) 1 ^ ei.1).prod

variable (Γ : List M)

theorem phi_def (p : List ℕ) :
    phi Γ p = (p.zipIdx.map fun ei => Γ.getD (ei.2 % Γ.length) 1 ^ ei.1).prod := (rfl)

@[simp]
theorem phi_nil : phi Γ [] = 1 := by
  simp [phi]

/-- `φ_{j+1,p} = φ_{j,p} * γ_{j+1} ^ p_{j+1}`, the indices of `Γ` being read modulo its
length. -/
@[simp]
theorem phi_concat (p : List ℕ) (e : ℕ) :
    phi Γ (p ++ [e]) = phi Γ p * Γ.getD (p.length % Γ.length) 1 ^ e := by
  simp [phi, List.zipIdx_append]

/-- For the empty sequence, `φ_{j,p}` is the identity. -/
@[simp]
theorem phi_nil_left (p : List ℕ) : phi ([] : List M) p = 1 := by
  simp [phi]

/-- `φ_{1,(e)} = γ₁ ^ e`. -/
@[simp]
theorem phi_singleton (e : ℕ) : phi Γ [e] = Γ.getD 0 1 ^ e := by
  simp [phi]

/-- `φ_{j,p}` is periodic: if the length of `p` is a multiple of the length of the sequence, then
`φ` of `p` followed by `q` is `φ` of `p` times `φ` of `q`. -/
theorem phi_append_of_dvd {p : List ℕ} (h : Γ.length ∣ p.length) (q : List ℕ) :
    phi Γ (p ++ q) = phi Γ p * phi Γ q := by
  obtain ⟨k, hk⟩ := h
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton q e ih =>
    rw [← List.append_assoc, phi_concat, ih, phi_concat, mul_assoc, List.length_append, hk,
      Nat.mul_add_mod]

/-- With all exponents zero, `φ_{j,p}` is the identity. -/
@[simp]
theorem phi_replicate_zero (j : ℕ) : phi Γ (List.replicate j 0) = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.replicate_succ', phi_concat, ih, pow_zero, mul_one]

/-- A monoid homomorphism carries `φ_{j,p}` of a sequence to `φ_{j,p}` of the image of the
sequence. -/
theorem map_phi {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F)
    (p : List ℕ) : f (phi Γ p) = phi (Γ.map f) p := by
  have hget (o : Option M) : f (o.getD 1) = (o.map f).getD 1 := by cases o <;> simp
  simp [phi, map_list_prod, Function.comp_def, hget]

end Phi

/-- For a sequence of automorphisms of `H`, the automorphisms `φ_{j,p}` fix every element fixed by
all the automorphisms of the sequence. -/
theorem phi_apply_of_forall_mem {H : Type*} [Mul H] {Γ : List (MulAut H)} {w : H}
    (h : ∀ γ ∈ Γ, γ w = w) (p : List ℕ) : phi Γ p w = w := by
  have hpow (γ : MulAut H) (hγ : γ w = w) (e : ℕ) : (γ ^ e) w = w := by
    induction e with
    | zero => simp
    | succ e ih => rw [pow_succ, MulAut.mul_apply, hγ, ih]
  induction p using List.reverseRecOn with
  | nil => simp
  | append_singleton p e ih =>
    rw [phi_concat, MulAut.mul_apply, hpow _ ?_, ih]
    obtain hlt | hle := lt_or_ge (p.length % Γ.length) Γ.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact h _ (List.getElem_mem hlt)
    · rw [List.getD_eq_default _ _ hle, MulAut.one_apply]

/-- For a sequence of automorphisms of `H`, the inverses of the automorphisms `φ_{j,p}` fix every
element fixed by all the automorphisms of the sequence. -/
theorem phi_symm_apply_of_forall_mem {H : Type*} [Mul H] {Γ : List (MulAut H)} {w : H}
    (h : ∀ γ ∈ Γ, γ w = w) (p : List ℕ) : (phi Γ p).symm w = w :=
  (phi Γ p).symm_apply_eq.2 (phi_apply_of_forall_mem h p).symm

section SeqPhi

variable {x y : Fin n → X} {z : Fin m → X} (inj : (Sum.elim (Sum.elim x y) z).Injective)
  (c : Fin m → G)

/-- The automorphisms `φ_{j,p}` of the basic sequence fix the word `S₀`. -/
@[simp]
theorem phi_basicWordSeq_basicWord (p : List ℕ) :
    phi (basicWordSeq inj c) p (basicWord x y z c) = basicWord x y z c :=
  phi_apply_of_forall_mem (fun _ hγ => apply_basicWord_of_mem_basicWordSeq inj c hγ) p

/-- The automorphisms `φ_{j,p}` of the basic sequence fix the coefficients. -/
@[simp]
theorem phi_basicWordSeq_inl (p : List ℕ) (g : G) : phi (basicWordSeq inj c) p (inl g) = inl g :=
  phi_apply_of_forall_mem (fun _ hγ => apply_inl_of_mem_basicWordSeq inj c hγ g) p

@[simp]
theorem phi_basicWordSeq_symm_basicWord (p : List ℕ) :
    (phi (basicWordSeq inj c) p).symm (basicWord x y z c) = basicWord x y z c :=
  phi_symm_apply_of_forall_mem (fun _ hγ => apply_basicWord_of_mem_basicWordSeq inj c hγ) p

@[simp]
theorem phi_basicWordSeq_symm_inl (p : List ℕ) (g : G) :
    (phi (basicWordSeq inj c) p).symm (inl g) = inl g :=
  phi_symm_apply_of_forall_mem (fun _ hγ => apply_inl_of_mem_basicWordSeq inj c hγ g) p

end SeqPhi

/-! ### Standard orientable quadratic equations -/

section Standard

open Quadratic Quadratic.Standard

variable {x y : Fin n → X} {z : Fin m → X}

variable {c : Fin m → G} {d : G}

/-- The inverse of the product of the atoms of the standard equation
`∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` is the word `S₀` of the mirrored variables and coefficients:
the indices are reversed, `x` and `y` are exchanged and the coefficients are inverted. -/
theorem basicWord_rev_eq_inv_prod_atoms_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    basicWord (y ∘ Fin.rev) (x ∘ Fin.rev) (z ∘ Fin.rev) (fun j => (c j.rev)⁻¹) =
      (orientableCoeff n m hnm x y z inj c hc d hd).atoms.prod⁻¹ := by
  rw [atoms_orientableCoeff, List.prod_append, mul_inv_rev, List.inv_prod_ofFn,
    List.inv_prod_ofFn, basicWord_def]
  refine congrArg₂ (· * ·) (congrArg List.prod (congrArg List.ofFn (funext fun j => ?_)))
    (congrArg List.prod (congrArg List.ofFn (funext fun i => ?_)))
  · simp [coeffAtom_def, mul_assoc]
  · simp [commAtom_def, commutatorElement_inv]

/-- The product of the atoms of the standard equation `∏ᵢ [xᵢ, yᵢ] d = 1` without coefficient
atoms is the word `S₀` of its variables. -/
theorem basicWord_eq_prod_atoms_orientableCoeff_zero {z : Fin 0 → X} {c : Fin 0 → G}
    (hn : 0 < n + 0) (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) :
    basicWord x y z c = (orientableCoeff n 0 hn x y z inj c hc d hd).atoms.prod := by
  simp [atoms_orientableCoeff, basicWord_def, funext (commAtom_def x y)]

/-- The product of the atoms of the standard equation `∏ᵢ [xᵢ, yᵢ] = 1` is the word `S₀` of its
variables. -/
theorem basicWord_eq_prod_atoms_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    basicWord x y Fin.elim0 (Fin.elim0 : Fin 0 → G) = (orientable n hn x y inj).atoms.prod := by
  simp [atoms_orientable, basicWord_def, funext (commAtom_def x y)]

/-- The basic sequence of automorphisms of `G[X]` of a standard orientable quadratic equation
`S = 1` ([IFT], §7.1). For an equation `∏ᵢ [xᵢ, yᵢ] = 1` or `∏ᵢ [xᵢ, yᵢ] d = 1` without
coefficient atoms it is `basicWordSeq` for the variables of the equation. An equation
`∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` with coefficient atoms is read backwards: the inverse of the
product of its atoms is `∏ⱼ zⱼ'⁻¹ cⱼ' zⱼ' ∏ᵢ [xᵢ', yᵢ']` for the mirrored variables and
coefficients `xᵢ' = y_{n+1-i}`, `yᵢ' = x_{n+1-i}`, `zⱼ' = z_{m+1-j}`, `cⱼ' = c_{m+1-j}⁻¹`
(indices from `1`; in Lean, `y ∘ Fin.rev`, `x ∘ Fin.rev`, `z ∘ Fin.rev` and
`fun j => (c j.rev)⁻¹`), and the sequence is `basicWordSeq` for these. -/
noncomputable def basicSeq : (S : Standard G X) → S.IsOrientable → List (MulAut (GX G X))
  | .orientable _ _ _ _ inj, _ => basicWordSeq (inj.sumElim_of_isEmpty Fin.elim0) Fin.elim0
  | .orientableCoeff _ m _ _ _ _ inj c _ _ _, _ =>
    if m = 0 then basicWordSeq inj c else
      basicWordSeq (inj.sumElim_sumElim_swap_comp Fin.rev_injective Fin.rev_injective
        Fin.rev_injective) fun j => (c j.rev)⁻¹
  | .nonorientable _ hn _ inj, h => (not_isOrientable_nonorientable hn inj h).elim
  | .nonorientableCoeff _ _ hn _ _ inj _ hc _ hd, h =>
    (not_isOrientable_nonorientableCoeff hn inj hc hd h).elim

theorem basicSeq_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    basicSeq (G := G) (orientable n hn x y inj) (isOrientable_orientable hn inj) =
      basicWordSeq (inj.sumElim_of_isEmpty Fin.elim0) Fin.elim0 := (rfl)

theorem basicSeq_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    basicSeq (orientableCoeff n m hnm x y z inj c hc d hd)
        (isOrientable_orientableCoeff hnm inj hc hd) =
      if m = 0 then basicWordSeq inj c else
        basicWordSeq (inj.sumElim_sumElim_swap_comp Fin.rev_injective Fin.rev_injective
          Fin.rev_injective) fun j => (c j.rev)⁻¹ := (rfl)

/-- Without coefficient atoms, the basic sequence of `∏ᵢ [xᵢ, yᵢ] d = 1` is the basic sequence of
the word `S₀` of its variables. -/
theorem basicSeq_orientableCoeff_of_eq_zero (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) (hm : m = 0) :
    basicSeq (orientableCoeff n m hnm x y z inj c hc d hd)
        (isOrientable_orientableCoeff hnm inj hc hd) = basicWordSeq inj c := by
  rw [basicSeq, ite_eq_left hm]

/-- With coefficient atoms, the basic sequence of `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` is the basic
sequence of the word `S₀` of the mirrored variables and coefficients. -/
theorem basicSeq_orientableCoeff_of_ne_zero (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) (hm : m ≠ 0) :
    basicSeq (orientableCoeff n m hnm x y z inj c hc d hd)
        (isOrientable_orientableCoeff hnm inj hc hd) =
      basicWordSeq (inj.sumElim_sumElim_swap_comp Fin.rev_injective Fin.rev_injective
        Fin.rev_injective) fun j => (c j.rev)⁻¹ := by
  rw [basicSeq, ite_eq_right hm]

variable {S : Standard G X} (hS : S.IsOrientable) {γ : MulAut (GX G X)}

/-- Every automorphism of the basic sequence fixes the coefficients. -/
theorem apply_inl_of_mem_basicSeq (hγ : γ ∈ basicSeq S hS) (g : G) : γ (inl g) = inl g := by
  cases S with
  | orientable n hn x y inj => exact apply_inl_of_mem_basicWordSeq _ _ hγ g
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rw [basicSeq] at hγ
    split_ifs at hγ <;> exact apply_inl_of_mem_basicWordSeq _ _ hγ g
  | nonorientable n hn x inj => exact (not_isOrientable_nonorientable hn inj hS).elim
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    exact (not_isOrientable_nonorientableCoeff hn inj hc hd hS).elim

/-- Every automorphism of the basic sequence of a standard orientable quadratic equation `S = 1`
fixes the product of the atoms of `S`. -/
theorem apply_prod_atoms_of_mem_basicSeq (hγ : γ ∈ basicSeq S hS) :
    γ S.atoms.prod = S.atoms.prod := by
  cases S with
  | orientable n hn x y inj =>
    simpa only [basicWord_eq_prod_atoms_orientable hn inj] using
      apply_basicWord_of_mem_basicWordSeq _ _ hγ
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rw [basicSeq] at hγ
    split_ifs at hγ with hm
    · subst hm
      simpa only [basicWord_eq_prod_atoms_orientableCoeff_zero hnm inj hc hd] using
        apply_basicWord_of_mem_basicWordSeq _ _ hγ
    · have h := apply_basicWord_of_mem_basicWordSeq _ _ hγ
      rwa [basicWord_rev_eq_inv_prod_atoms_orientableCoeff hnm inj hc hd, map_inv, inv_inj] at h
  | nonorientable n hn x inj => exact (not_isOrientable_nonorientable hn inj hS).elim
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    exact (not_isOrientable_nonorientableCoeff hn inj hc hd hS).elim

/-- Every automorphism of the basic sequence of a standard orientable quadratic equation `S = 1`
fixes the left side of `S`. -/
theorem apply_toWord_of_mem_basicSeq (hγ : γ ∈ basicSeq S hS) : γ S.toWord = S.toWord := by
  rw [toWord_def, map_mul, apply_prod_atoms_of_mem_basicSeq hS hγ,
    apply_inl_of_mem_basicSeq hS hγ]

/-- The automorphisms `φ_{j,p}` of a standard orientable quadratic equation `S = 1` fix the left
side of `S`. -/
@[simp]
theorem phi_basicSeq_toWord (p : List ℕ) : phi (basicSeq S hS) p S.toWord = S.toWord :=
  phi_apply_of_forall_mem (fun _ hγ => apply_toWord_of_mem_basicSeq hS hγ) p

/-- The automorphisms `φ_{j,p}` of a standard orientable quadratic equation fix the
coefficients. -/
@[simp]
theorem phi_basicSeq_inl (p : List ℕ) (g : G) : phi (basicSeq S hS) p (inl g) = inl g :=
  phi_apply_of_forall_mem (fun _ hγ => apply_inl_of_mem_basicSeq hS hγ g) p

@[simp]
theorem phi_basicSeq_symm_toWord (p : List ℕ) : (phi (basicSeq S hS) p).symm S.toWord = S.toWord :=
  phi_symm_apply_of_forall_mem (fun _ hγ => apply_toWord_of_mem_basicSeq hS hγ) p

@[simp]
theorem phi_basicSeq_symm_inl (p : List ℕ) (g : G) : (phi (basicSeq S hS) p).symm (inl g) = inl g :=
  phi_symm_apply_of_forall_mem (fun _ hγ => apply_inl_of_mem_basicSeq hS hγ g) p

variable {H : Type*} [Group H] (ι : G →* H)

/-- Every automorphism of the basic sequence of a standard orientable quadratic equation `S = 1`
permutes the solutions of `S = 1`: a point `v` is a solution exactly when the point
`x ↦ (γ x)(v)` is. -/
theorem wordMap_mem_V_iff_of_mem_basicSeq (hγ : γ ∈ basicSeq S hS) (v : X → H) :
    wordMap ι (fun x => γ (inr (.of x))) v ∈ V ι {S.toWord} ↔ v ∈ V ι {S.toWord} := by
  have h := DFunLike.congr_fun
    (eval_wordMap (ι := ι) (.ofMulEquiv γ fun g => apply_inl_of_mem_basicSeq hS hγ g) v) S.toWord
  simp_all [apply_toWord_of_mem_basicSeq hS hγ]

/-- For a standard orientable quadratic equation `S = 1`, the value of the left side of `S` at the
point `x ↦ (φ_{j,p} x)(v)` is its value at `v`. -/
@[simp]
theorem eval_wordMap_phi_basicSeq_toWord (p : List ℕ) (v : X → H) :
    eval ι (wordMap ι (fun x => phi (basicSeq S hS) p (inr (.of x))) v) S.toWord =
      eval ι v S.toWord := by
  have h := DFunLike.congr_fun
    (eval_wordMap (ι := ι) (.ofMulEquiv (phi (basicSeq S hS) p) (phi_basicSeq_inl hS p)) v)
    S.toWord
  simp_all

/-- The automorphisms `φ_{j,p}` of a standard orientable quadratic equation `S = 1` permute the
solutions of `S = 1`: a point `v` is a solution exactly when the point `x ↦ (φ_{j,p} x)(v)` is. -/
theorem wordMap_phi_basicSeq_mem_V_iff (p : List ℕ) (v : X → H) :
    wordMap ι (fun x => phi (basicSeq S hS) p (inr (.of x))) v ∈ V ι {S.toWord} ↔
      v ∈ V ι {S.toWord} := by
  simp

/-- The basic sequence of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` has `4n - 1` terms. -/
@[simp]
theorem length_basicSeq_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (basicSeq (G := G) (orientable n hn x y inj) (isOrientable_orientable hn inj)).length =
      4 * n - 1 := by
  rw [basicSeq_orientable hn inj, length_basicWordSeq]
  simp

/-- The basic sequence of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` has `K(m, n)` terms:
`m + 4n - 1` when `m, n ≠ 0`, `4n - 1` when `m = 0` and `m - 1` when `n = 0`. -/
@[simp]
theorem length_basicSeq_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (basicSeq (orientableCoeff n m hnm x y z inj c hc d hd)
        (isOrientable_orientableCoeff hnm inj hc hd)).length =
      (m - 1) + (if 0 < m ∧ 0 < n then 1 else 0) + (4 * n - 1) := by
  rw [basicSeq, apply_ite List.length,
    length_basicWordSeq, length_basicWordSeq, ite_self]

end Standard

/-! ### Examples -/

section Examples

open Quadratic.Standard

variable {x y : Fin 2 → X} (inj : (Sum.elim x y).Injective)

/-- The basic sequence of the genus-two equation `[x₁, y₁][x₂, y₂] = 1` has `7` terms. -/
theorem length_basicSeq_genusTwo :
    (basicSeq (G := G) (orientable 2 Nat.zero_lt_two x y inj)
      (isOrientable_orientable _ inj)).length = 7 := by
  rw [length_basicSeq_orientable]

/-- Every automorphism of the basic sequence of `[x₁, y₁][x₂, y₂] = 1` fixes the word
`[x₁, y₁][x₂, y₂]`. -/
theorem apply_genusTwo_of_mem_basicSeq {γ : MulAut (GX G X)}
    (hγ : γ ∈ basicSeq (orientable 2 Nat.zero_lt_two x y inj) (isOrientable_orientable _ inj)) :
    γ (⁅(inr (.of (x 0)) : GX G X)⁻¹, (inr (.of (y 0)))⁻¹⁆ *
        ⁅(inr (.of (x 1)) : GX G X)⁻¹, (inr (.of (y 1)))⁻¹⁆) =
      ⁅(inr (.of (x 0)) : GX G X)⁻¹, (inr (.of (y 0)))⁻¹⁆ *
        ⁅(inr (.of (x 1)) : GX G X)⁻¹, (inr (.of (y 1)))⁻¹⁆ := by
  simpa [List.ofFn_succ] using apply_prod_atoms_of_mem_basicSeq _ hγ

/-- The basic sequence of a standard equation `z₁⁻¹ c₁ z₁ · z₂⁻¹ c₂ z₂ · z₃⁻¹ c₃ z₃ · d = 1`
without commutators has `K(3, 0) = 2` terms. -/
theorem length_basicSeq_conjugates {z : Fin 3 → X} {c : Fin 3 → G} {d : G}
    (inj : (Sum.elim (Sum.elim Fin.elim0 Fin.elim0) z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) :
    (basicSeq (orientableCoeff 0 3 (by omega) Fin.elim0 Fin.elim0 z inj c hc d hd)
      (isOrientable_orientableCoeff _ inj hc hd)).length = 2 := by
  rw [length_basicSeq_orientableCoeff]
  simp

end Examples

end TauCeti.GroupAlgGeom.Lift
