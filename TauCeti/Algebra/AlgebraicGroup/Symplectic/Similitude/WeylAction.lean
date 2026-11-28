/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.WeylGroup
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Similitude.Weight

/-!
# The reciprocal Weyl action on the Laurent character algebra of `GSp₂g`

Characters of algebraic representations of `GSp₂g` restricted to its diagonal torus
`diag(z₁, …, z_g, t/z₁, …, t/z_g)` are Laurent polynomials in the independent coordinates
`t, z₁, …, z_g` with integer coefficients: elements of the integral group algebra
`L_g = ℤ[X_g]` of the weight lattice `X_g = ℤ × ℤ^g` (`TauCeti.SymplecticSimilitude.Laurent`).

The Weyl group is the hyperoctahedral group `Sym(Bool) ≀ Sym(g)` of signed permutations of the
`g` hyperbolic pairs. It acts on `X_g` *reciprocally*: a permutation `σ` relabels the pairs,
`(m, u) ↦ (m, u ∘ σ⁻¹)`, while the flip of pair `i` exchanges `zᵢ` with `t/zᵢ` and fixes `t`,
`(m, u) ↦ (m + uᵢ, u[i := -uᵢ])`. In general a signed permutation `w` acts on `u` exactly as the
Weyl group of `Sp₂g` does (`TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup`), and the
multiplier exponent is the unique one for which the central degree `2m + ∑ uᵢ` is preserved. This
is not the action `zᵢ ↦ zᵢ⁻¹` with `t` fixed: the flip sends `z²` to `t²/z²`, not to `z⁻²`.

The Weyl-invariant elements of `L_g` form the subring
`TauCeti.SymplecticSimilitude.invariantSubring`. It is the ring in which torus characters of
algebraic representations of `GSp₂g` take values, and the subring that the integral polynomial
presentations of the character rings of `GSp₂g` describe.

## Main declarations

* `TauCeti.SymplecticSimilitude.Laurent` and `TauCeti.SymplecticSimilitude.monomial`: the
  integral group algebra of `X_g` and its basis monomials `t^m z^u`.
* `TauCeti.SymplecticSimilitude.weylWeight`: the action of a signed permutation on `X_g`, a group
  action (`weylWeight_mul`, `weylWeight_one`) preserving the central degree
  (`centralDegree_weylWeight`) and covering the Weyl action on the character lattice of the
  diagonal torus of `Sp₂g` (`toGspCharacterLattice_weylWeight_fst`).
* `TauCeti.SymplecticSimilitude.permWeight` and `TauCeti.SymplecticSimilitude.flipWeight`: the
  generators, with the formulas `permWeight_apply` and `flipWeight_apply`, and the relations
  `flipWeight_flipWeight`, `flipWeight_comm` and `permWeight_flipWeight_permWeight_symm`.
* `TauCeti.SymplecticSimilitude.weylLaurent`: the induced group homomorphism from
  `Sym(Bool) ≀ Sym(g)` to the `ℤ`-algebra automorphisms of `L_g`, with its generators
  `TauCeti.SymplecticSimilitude.permLaurent` and `TauCeti.SymplecticSimilitude.flipLaurent`.
* `TauCeti.SymplecticSimilitude.invariantSubring`: the Weyl-invariant Laurent polynomials, with
  `mem_invariantSubring_iff`: invariance under the whole Weyl group is invariance under the pair
  permutations and the pair flips.

## References

* H. Yu, *Number of irreducible ℓ-adic local systems on a curve*, arXiv:1807.04659v5, §7.1,
  equation (7.1.1) and Remark 7.1.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III (the Weyl group of `Cₘ`).
-/

public section

noncomputable section

open Function

namespace TauCeti.SymplecticSimilitude

variable {g : ℕ}

/-! ### The Laurent character algebra -/

/-- **The Laurent character algebra** `L_g = ℤ[X_g]` of the diagonal torus of `GSp₂g`: the
integral group algebra of the weight lattice, whose basis monomials `t^m z₁^u₁ ⋯ z_g^u_g` are
indexed by the weights `(m, u)`. -/
abbrev Laurent (g : ℕ) := MonoidAlgebra ℤ (Multiplicative (Weight g))

/-- The basis monomial `t^m z₁^u₁ ⋯ z_g^u_g` of the weight `(m, u)`, with coefficient `1`. For
instance `monomial (multiplierWeight g)` is `t`, `monomial (standardWeight i)` is `zᵢ` and
`monomial (pairedWeight i)` is `t/zᵢ`. -/
def monomial (wt : Weight g) : Laurent g :=
  MonoidAlgebra.of ℤ (Multiplicative (Weight g)) (Multiplicative.ofAdd wt)

theorem monomial_eq_single (wt : Weight g) :
    monomial wt = MonoidAlgebra.single (Multiplicative.ofAdd wt) 1 :=
  (rfl)

@[simp]
theorem monomial_zero : monomial (0 : Weight g) = 1 :=
  map_one (MonoidAlgebra.of ℤ (Multiplicative (Weight g)))

theorem monomial_add (a b : Weight g) : monomial (a + b) = monomial a * monomial b :=
  map_mul (MonoidAlgebra.of ℤ (Multiplicative (Weight g))) (.ofAdd a) (.ofAdd b)

/-- The monomial of `-wt` is the inverse of the monomial of `wt`; for instance `t⁻¹ t = 1`. -/
@[simp]
theorem monomial_neg_mul_monomial (wt : Weight g) : monomial (-wt) * monomial wt = 1 := by
  rw [← monomial_add, neg_add_cancel, monomial_zero]

/-- Distinct weights have distinct monomials. -/
theorem monomial_injective : Injective (monomial (g := g)) :=
  (MonoidAlgebra.of_injective (R := ℤ)).comp Multiplicative.ofAdd.injective

@[simp]
theorem monomial_inj {a b : Weight g} : monomial a = monomial b ↔ a = b :=
  monomial_injective.eq_iff

@[simp]
theorem coeff_monomial (wt wt' : Weight g) :
    (monomial wt).coeff (Multiplicative.ofAdd wt') = if wt = wt' then 1 else 0 := by
  simp [monomial_eq_single, Finsupp.single_apply]

/-! ### The Weyl action on the weight lattice -/

/-- The action of a signed permutation on `X_g`, as an additive map; it is upgraded to an additive
equivalence in `weylWeight`. -/
private def weylWeightHom (w : WreathProduct (Equiv.Perm Bool) (Fin g)) : Weight g →+ Weight g where
  toFun wt :=
    (wt.1 + ∑ b, if w.left b false then wt.2 (w.right.symm b) else 0,
      fun b ↦ if w.left b false then -wt.2 (w.right.symm b) else wt.2 (w.right.symm b))
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext b'
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [add_add_add_comm, ← Finset.sum_add_distrib]
      congr 2 with c
      split_ifs <;> simp
    · simp only [Prod.snd_add, Pi.add_apply]
      split_ifs <;> abel

/-- The Weyl action on the `Sp₂g` part of a weight is the Weyl action of
`TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup`. -/
private theorem toGspCharacterLattice_weylWeightHom_fst
    (w : WreathProduct (Equiv.Perm Bool) (Fin g)) (wt : Weight g) :
    (toGspCharacterLattice g (weylWeightHom w wt)).1 =
      Symplectic.diagonalWreathProductMulEquivWeylGroup.{0} g w •
        (toGspCharacterLattice g wt).1 := by
  ext ⟨b⟩
  simp [weylWeightHom]

private theorem centralDegree_weylWeightHom (w : WreathProduct (Equiv.Perm Bool) (Fin g))
    (wt : Weight g) : centralDegree g (weylWeightHom w wt) = centralDegree g wt := by
  have hsum : ∑ b, wt.2 (w.right.symm b) = ∑ b, wt.2 b := w.right.symm.sum_comp wt.2
  simp only [weylWeightHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, centralDegree_apply]
  rw [← hsum, mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 2 with b
  split_ifs <;> ring

/-- A weight is determined by its `Sp₂g` part, transported to the character lattice of
`TauCeti.gspRootDatum`, and its central degree. -/
private theorem eq_of_toGspCharacterLattice_fst_eq {a b : Weight g}
    (h₁ : (toGspCharacterLattice g a).1 = (toGspCharacterLattice g b).1)
    (h₂ : centralDegree g a = centralDegree g b) : a = b := by
  refine coverPullback_injective ?_
  rw [coverPullback_apply, coverPullback_apply, h₂]
  congr 1
  funext i
  simpa using congrArg (· (ULift.up i)) h₁

private theorem weylWeightHom_mul (w v : WreathProduct (Equiv.Perm Bool) (Fin g))
    (wt : Weight g) : weylWeightHom (w * v) wt = weylWeightHom w (weylWeightHom v wt) := by
  refine eq_of_toGspCharacterLattice_fst_eq ?_ ?_
  · simp only [toGspCharacterLattice_weylWeightHom_fst, map_mul, mul_smul]
  · simp only [centralDegree_weylWeightHom]

private theorem weylWeightHom_one (wt : Weight g) : weylWeightHom 1 wt = wt := by
  refine eq_of_toGspCharacterLattice_fst_eq ?_ ?_
  · simp only [toGspCharacterLattice_weylWeightHom_fst, map_one, one_smul]
  · simp only [centralDegree_weylWeightHom]

/-- **The Weyl action on the weight lattice.** A signed permutation `w`, with permutation
`π = w.right` of the pairs, sends `(m, u)` to `(m', u')`, where `u'_b = ± u_{π⁻¹ b}`, negated
exactly when `w` flips the pair `b`, and `m' = m + ∑ u_{π⁻¹ b}` over the flipped pairs `b`. -/
def weylWeight (w : WreathProduct (Equiv.Perm Bool) (Fin g)) : Weight g ≃+ Weight g where
  __ := weylWeightHom w
  invFun := weylWeightHom w⁻¹
  left_inv wt := by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    rw [← weylWeightHom_mul, inv_mul_cancel, weylWeightHom_one]
  right_inv wt := by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    rw [← weylWeightHom_mul, mul_inv_cancel, weylWeightHom_one]

theorem weylWeight_apply (w : WreathProduct (Equiv.Perm Bool) (Fin g)) (wt : Weight g) :
    weylWeight w wt =
      (wt.1 + ∑ b, if w.left b false then wt.2 (w.right.symm b) else 0,
        fun b ↦ if w.left b false then -wt.2 (w.right.symm b) else wt.2 (w.right.symm b)) :=
  (rfl)

/-- The Weyl action is an action: `weylWeight (w * v) = weylWeight w ∘ weylWeight v`. -/
theorem weylWeight_mul (w v : WreathProduct (Equiv.Perm Bool) (Fin g)) (wt : Weight g) :
    weylWeight (w * v) wt = weylWeight w (weylWeight v wt) :=
  weylWeightHom_mul w v wt

@[simp]
theorem weylWeight_one (wt : Weight g) : weylWeight 1 wt = wt :=
  weylWeightHom_one wt

@[simp]
theorem weylWeight_symm (w : WreathProduct (Equiv.Perm Bool) (Fin g)) :
    (weylWeight w).symm = weylWeight w⁻¹ :=
  AddEquiv.ext fun _ ↦ (rfl)

/-- **The Weyl action preserves the central degree** `2m + ∑ uᵢ`: the Weyl group commutes with
the centre. -/
@[simp]
theorem centralDegree_weylWeight (w : WreathProduct (Equiv.Perm Bool) (Fin g)) (wt : Weight g) :
    centralDegree g (weylWeight w wt) = centralDegree g wt :=
  centralDegree_weylWeightHom w wt

/-- **The Weyl action covers the Weyl action of `Sp₂g`**: under the projection `(m, u) ↦ u` to the
character lattice of the diagonal torus of `Sp₂g`, a signed permutation acts through
`TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup`. -/
theorem toGspCharacterLattice_weylWeight_fst (w : WreathProduct (Equiv.Perm Bool) (Fin g))
    (wt : Weight g) :
    (toGspCharacterLattice g (weylWeight w wt)).1 =
      Symplectic.diagonalWreathProductMulEquivWeylGroup.{0} g w •
        (toGspCharacterLattice g wt).1 :=
  toGspCharacterLattice_weylWeightHom_fst w wt

/-- The Weyl group fixes the multiplier weight `e_t`: every Weyl element fixes `t`. -/
@[simp]
theorem weylWeight_multiplierWeight (w : WreathProduct (Equiv.Perm Bool) (Fin g)) :
    weylWeight w (multiplierWeight g) = multiplierWeight g := by
  ext <;> simp [weylWeight_apply]

/-! ### Pair permutations and pair flips -/

/-- **The permutation of the pairs** by `σ`: `(m, u) ↦ (m, u ∘ σ⁻¹)`, sending `zᵢ` to `z_{σ i}`. -/
def permWeight (σ : Equiv.Perm (Fin g)) : Weight g ≃+ Weight g :=
  weylWeight (SemidirectProduct.inr σ)

/-- **The flip of the pair `i`**: `(m, u) ↦ (m + uᵢ, u[i := -uᵢ])`, exchanging `zᵢ` and `t/zᵢ`. -/
def flipWeight (i : Fin g) : Weight g ≃+ Weight g :=
  weylWeight (SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true)))

theorem permWeight_apply (σ : Equiv.Perm (Fin g)) (wt : Weight g) :
    permWeight σ wt = (wt.1, fun i ↦ wt.2 (σ.symm i)) := by
  simp [permWeight, weylWeight_apply]

theorem flipWeight_apply (i : Fin g) (wt : Weight g) :
    flipWeight i wt = (wt.1 + wt.2 i, update wt.2 i (-wt.2 i)) := by
  rw [flipWeight, weylWeight_apply]
  ext j
  · simp [Pi.mulSingle_apply, apply_ite (fun e : Equiv.Perm Bool ↦ e false), ← Equiv.Perm.inv_def]
  · by_cases h : j = i
    · subst h
      simp [← Equiv.Perm.inv_def]
    · simp [h, ← Equiv.Perm.inv_def]

@[simp]
theorem permWeight_apply_fst (σ : Equiv.Perm (Fin g)) (wt : Weight g) :
    (permWeight σ wt).1 = wt.1 := by
  simp [permWeight_apply]

@[simp]
theorem permWeight_apply_snd (σ : Equiv.Perm (Fin g)) (wt : Weight g) (i : Fin g) :
    (permWeight σ wt).2 i = wt.2 (σ.symm i) := by
  simp [permWeight_apply]

@[simp]
theorem flipWeight_apply_fst (i : Fin g) (wt : Weight g) :
    (flipWeight i wt).1 = wt.1 + wt.2 i := by
  simp [flipWeight_apply]

@[simp]
theorem flipWeight_apply_snd (i : Fin g) (wt : Weight g) :
    (flipWeight i wt).2 = update wt.2 i (-wt.2 i) := by
  simp [flipWeight_apply]

@[simp]
theorem permWeight_standardWeight (σ : Equiv.Perm (Fin g)) (i : Fin g) :
    permWeight σ (standardWeight i) = standardWeight (σ i) := by
  ext j
  · simp
  · simp [Pi.single_apply, Equiv.symm_apply_eq]

@[simp]
theorem permWeight_pairedWeight (σ : Equiv.Perm (Fin g)) (i : Fin g) :
    permWeight σ (pairedWeight i) = pairedWeight (σ i) := by
  rw [eq_sub_of_add_eq' (standardWeight_add_pairedWeight i), map_sub, permWeight_standardWeight,
    eq_sub_of_add_eq' (standardWeight_add_pairedWeight (σ i)), permWeight,
    weylWeight_multiplierWeight]

/-- The flip of pair `i` sends `zᵢ` to `t/zᵢ`. -/
@[simp]
theorem flipWeight_standardWeight (i : Fin g) :
    flipWeight i (standardWeight i) = pairedWeight i := by
  ext j
  · simp
  · by_cases h : j = i
    · subst h
      simp
    · simp [h]

/-- Each pair flip is an involution. -/
@[simp]
theorem flipWeight_flipWeight (i : Fin g) (wt : Weight g) :
    flipWeight i (flipWeight i wt) = wt := by
  rw [flipWeight, ← weylWeight_mul, ← map_mul, ← Pi.mulSingle_mul, Equiv.swap_mul_self,
    Pi.mulSingle_one, map_one, weylWeight_one]

/-- The flip of pair `i` sends `t/zᵢ` to `zᵢ`. -/
@[simp]
theorem flipWeight_pairedWeight (i : Fin g) :
    flipWeight i (pairedWeight i) = standardWeight i := by
  rw [← flipWeight_standardWeight i, flipWeight_flipWeight]

/-- The flip of pair `i` fixes `zⱼ` for `j ≠ i`. -/
@[simp]
theorem flipWeight_standardWeight_of_ne {i j : Fin g} (h : j ≠ i) :
    flipWeight i (standardWeight j) = standardWeight j := by
  ext k
  · simp [Ne.symm h]
  · by_cases hk : k = i
    · subst hk
      simp [Ne.symm h]
    · simp [hk]

/-- The flip of pair `i` fixes `t/zⱼ` for `j ≠ i`. -/
@[simp]
theorem flipWeight_pairedWeight_of_ne {i j : Fin g} (h : j ≠ i) :
    flipWeight i (pairedWeight j) = pairedWeight j := by
  rw [eq_sub_of_add_eq' (standardWeight_add_pairedWeight j), map_sub,
    flipWeight_standardWeight_of_ne h, flipWeight, weylWeight_multiplierWeight]

/-- Pair flips commute with one another. -/
theorem flipWeight_comm (i j : Fin g) (wt : Weight g) :
    flipWeight i (flipWeight j wt) = flipWeight j (flipWeight i wt) := by
  by_cases h : i = j
  · rw [h]
  · simp only [flipWeight, ← weylWeight_mul, ← map_mul, (Pi.mulSingle_commute h _ _).eq]

/-- Conjugating the flip of pair `i` by a permutation `σ` of the pairs gives the flip of the
pair `σ i`. -/
theorem permWeight_flipWeight_permWeight_symm (σ : Equiv.Perm (Fin g)) (i : Fin g)
    (wt : Weight g) :
    permWeight σ (flipWeight i (permWeight σ.symm wt)) = flipWeight (σ i) wt := by
  ext j
  · simp
  · by_cases h : j = σ i
    · subst h
      simp
    · simp [h, Equiv.symm_apply_eq]

/-- Every pair permutation preserves the central degree. -/
theorem centralDegree_permWeight (σ : Equiv.Perm (Fin g)) (wt : Weight g) :
    centralDegree g (permWeight σ wt) = centralDegree g wt :=
  centralDegree_weylWeight _ wt

/-- Every pair flip preserves the central degree. -/
theorem centralDegree_flipWeight (i : Fin g) (wt : Weight g) :
    centralDegree g (flipWeight i wt) = centralDegree g wt :=
  centralDegree_weylWeight _ wt

/-! ### The Weyl action on the Laurent character algebra -/

/-- **The Weyl action on the Laurent character algebra**: the group homomorphism from
`Sym(Bool) ≀ Sym(g)` to the `ℤ`-algebra automorphisms of `L_g` that moves each monomial by
`weylWeight`. -/
def weylLaurent (g : ℕ) :
    WreathProduct (Equiv.Perm Bool) (Fin g) →* (Laurent g ≃ₐ[ℤ] Laurent g) :=
  MonoidAlgebra.domCongrAut.comp
    { toFun w := AddEquiv.toMultiplicative (weylWeight w)
      map_one' := MulEquiv.ext fun _ ↦ congrArg Multiplicative.ofAdd (weylWeight_one _)
      map_mul' w v := MulEquiv.ext fun _ ↦ congrArg Multiplicative.ofAdd (weylWeight_mul w v _) }

/-- The Weyl action moves the monomial of `wt` to the monomial of `weylWeight w wt`. -/
@[simp]
theorem weylLaurent_monomial (w : WreathProduct (Equiv.Perm Bool) (Fin g)) (wt : Weight g) :
    weylLaurent g w (monomial wt) = monomial (weylWeight w wt) := by
  simp [weylLaurent, monomial_eq_single]

/-- The coefficient of `weylLaurent g w f` at `wt` is the coefficient of `f` at
`(weylWeight w)⁻¹ wt`. -/
@[simp]
theorem coeff_weylLaurent (w : WreathProduct (Equiv.Perm Bool) (Fin g)) (f : Laurent g)
    (wt : Weight g) :
    (weylLaurent g w f).coeff (Multiplicative.ofAdd wt) =
      f.coeff (Multiplicative.ofAdd (weylWeight w⁻¹ wt)) := by
  simp [weylLaurent]

/-- **The permutation of the pairs** by `σ`, as a `ℤ`-algebra automorphism of `L_g`: it sends
`zᵢ` to `z_{σ i}` and `t/zᵢ` to `t/z_{σ i}`. -/
def permLaurent (σ : Equiv.Perm (Fin g)) : Laurent g ≃ₐ[ℤ] Laurent g :=
  weylLaurent g (SemidirectProduct.inr σ)

/-- **The flip of the pair `i`**, as a `ℤ`-algebra automorphism of `L_g`: it exchanges `zᵢ` and
`t/zᵢ`, fixing `t` and the other pairs. -/
def flipLaurent (i : Fin g) : Laurent g ≃ₐ[ℤ] Laurent g :=
  weylLaurent g (SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true)))

@[simp]
theorem permLaurent_monomial (σ : Equiv.Perm (Fin g)) (wt : Weight g) :
    permLaurent σ (monomial wt) = monomial (permWeight σ wt) :=
  weylLaurent_monomial _ wt

@[simp]
theorem flipLaurent_monomial (i : Fin g) (wt : Weight g) :
    flipLaurent i (monomial wt) = monomial (flipWeight i wt) :=
  weylLaurent_monomial _ wt

/-! ### The Weyl-invariant subring -/

/-- **The Weyl-invariant Laurent polynomials** `L_g^W`: the elements of `L_g` fixed by every
signed permutation of the pairs. By `mem_invariantSubring_iff`, these are the elements fixed by
every pair permutation and every pair flip. -/
def invariantSubring (g : ℕ) : Subring (Laurent g) :=
  ⨅ w, RingHom.eqLocus (weylLaurent g w : Laurent g →+* Laurent g) (RingHom.id _)

theorem mem_invariantSubring {f : Laurent g} :
    f ∈ invariantSubring g ↔ ∀ w, weylLaurent g w f = f := by
  simp [invariantSubring, Subring.mem_iInf]

/-- **Invariance under generators.** A Laurent polynomial is Weyl invariant exactly when it is
fixed by every permutation of the pairs and by every pair flip. -/
theorem mem_invariantSubring_iff {f : Laurent g} :
    f ∈ invariantSubring g ↔ (∀ σ, permLaurent σ f = f) ∧ ∀ i, flipLaurent i f = f := by
  refine ⟨fun h ↦ ⟨fun σ ↦ mem_invariantSubring.mp h _, fun i ↦ mem_invariantSubring.mp h _⟩,
    fun ⟨hσ, hi⟩ ↦ mem_invariantSubring.mpr fun w ↦ ?_⟩
  let H : Subgroup (WreathProduct (Equiv.Perm Bool) (Fin g)) :=
    (MulAction.stabilizer (Laurent g ≃ₐ[ℤ] Laurent g) f).comap (weylLaurent g)
  exact WreathProduct.mem_of_inl_mulSingle_swap_mem_of_inr_swap_mem (H := H) (fun i ↦ hi i)
    (fun i j _ ↦ hσ (Equiv.swap i j)) w

/-- A monomial is Weyl invariant exactly when its weight is fixed by every Weyl element. -/
theorem monomial_mem_invariantSubring_iff {wt : Weight g} :
    monomial wt ∈ invariantSubring g ↔ ∀ w, weylWeight w wt = wt := by
  simp [mem_invariantSubring]

/-- The multiplier monomial `t` is Weyl invariant. -/
theorem monomial_multiplierWeight_mem_invariantSubring :
    monomial (multiplierWeight g) ∈ invariantSubring g :=
  monomial_mem_invariantSubring_iff.mpr weylWeight_multiplierWeight

/-- The inverse multiplier monomial `t⁻¹` is Weyl invariant. -/
theorem monomial_neg_multiplierWeight_mem_invariantSubring :
    monomial (-multiplierWeight g) ∈ invariantSubring g :=
  monomial_mem_invariantSubring_iff.mpr fun w ↦ by rw [map_neg, weylWeight_multiplierWeight]

/-- The character `∑ᵢ (zᵢ + t/zᵢ)` of the standard representation is Weyl invariant. -/
theorem sum_monomial_standardWeight_add_monomial_pairedWeight_mem_invariantSubring :
    ∑ i, (monomial (standardWeight i) + monomial (pairedWeight i)) ∈ invariantSubring g := by
  refine mem_invariantSubring_iff.mpr ⟨fun σ ↦ ?_, fun i ↦ ?_⟩
  · simp only [map_sum, map_add, permLaurent_monomial, permWeight_standardWeight,
      permWeight_pairedWeight]
    exact Equiv.sum_comp σ fun i ↦ monomial (standardWeight i) + monomial (pairedWeight i)
  · simp only [map_sum, map_add, flipLaurent_monomial]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases h : j = i
    · subst h
      rw [flipWeight_standardWeight, flipWeight_pairedWeight, add_comm]
    · rw [flipWeight_standardWeight_of_ne h, flipWeight_pairedWeight_of_ne h]

end TauCeti.SymplecticSimilitude

end
