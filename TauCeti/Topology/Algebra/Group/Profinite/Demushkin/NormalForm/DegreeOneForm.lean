/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.GradedClass
public import TauCeti.Topology.Algebra.Group.Profinite.Free.DegreeOneForm
import Mathlib.Algebra.CharP.Reduced
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Labute's normal forms modulo `λ_2`

Let `F = freeProP p (Fin n)` be the free pro-`p` group on `n` generators `x₁, …, x_n`, let
`gr_1(F) = λ_1(F) ⧸ λ_2(F)` be the degree-one piece of its lower `p`-series, and let `ρ ∈ gr_1(F)`
be a class whose degree-one form `TauCeti.freeProP.degreeOneForm ρ` — the bilinear form on the
continuous `𝔽_p`-dual of `F` whose matrix carries the commutator coordinates of `ρ` off the
diagonal and `(p choose 2)` times its `p`-power coordinates on it — is nondegenerate. For the
class of a relator `r` this is the form Labute reads off `r` to describe the cup product on
`H¹(F ⧸ ⟪r⟫, 𝔽_p)` (Labute, Proposition 3); that identification is not made here. This file proves
Labute's normal forms for such a class modulo `λ_2`: a continuous automorphism of `F` carries `ρ`
to the class of one of the normal-form relator words,

* `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` or `x₁^p (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, and then `n`
  is even, when the form is alternating, which is automatic for odd `p`
  (`TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo`); at
  `p = 2` only the first word occurs
  (`exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo_zero_of_two`);
* `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`, which is `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` modulo `λ_2`,
  when `p = 2`, the form is not alternating and `n` is odd
  (`TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd`, and
  `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOddTop` for
  the word at `f = ∞` itself);
* `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, which is
  `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` modulo `λ_2`, when `p = 2`, the form is not alternating
  and `n` is even
  (`TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven`).

The route follows Labute. Every basis of the continuous dual is realized by a continuous
automorphism of `F` (`TauCeti.freeProP.exists_continuousMulEquiv_continuousZModDualMap_eq`), so
the normal forms of bilinear forms apply. In the alternating case a symplectic basis, interleaved
so that the hyperbolic pairs become the pairs `(x_{2a+1}, x_{2a+2})`, brings the commutator
coordinates into the shape `(x₁, x₂)(x₃, x₄) ⋯`. The `p`-power coordinates are invisible to the
form for odd `p`; they define a functional `ℓ` on the dual, and if `ℓ ≠ 0` the symplectic basis is
chosen through a hyperbolic pair `(θ, e₀)` with `θ` representing `ℓ`, so that `ℓ` vanishes on every
basis vector but `e₀`, and the `p`-power part becomes exactly `π ξ₁`. In the nonalternating case,
which occurs only at `p = 2`, the form is symmetric and any two nondegenerate symmetric
nonalternating forms of the same dimension are equivalent, while at `p = 2` the form determines
the class; it therefore suffices to check that the forms of the two dyadic normal-form words are
nondegenerate and not alternating, which is a direct computation.

## Main results

* `TauCeti.freeProP.degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl`: the `p`-power
  coordinates of the class of `x₁^q (x₁, x₂) ⋯` are `q / p` at `x₁` and `0` elsewhere.
* `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo`: the
  alternating case, for every `p`.
* `TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordNeTwo`: the degree-one form of the
  normal-form word `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` is nondegenerate for `n` even and every `q`
  divisible by `p` (at `p = 2` this includes `q ≡ 2 mod 4`, where the form is not alternating).
* `TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordTwoOdd`,
  `TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordTwoEven`: the degree-one forms of
  the two dyadic normal-form words are nondegenerate, for `n` odd, resp. even, for every `f ≥ 1`
  and every even `a`; under the normal-form bounds `f ≥ 2` and `4 ∣ a` they are moreover not
  alternating (`TauCeti.freeProP.not_isAlt_degreeOneForm_demushkinWordTwoOdd`,
  `TauCeti.freeProP.not_isAlt_degreeOneForm_demushkinWordTwoEven`);
  `TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordTwoOddTop` and
  `TauCeti.freeProP.not_isAlt_degreeOneForm_demushkinWordTwoOddTop`: the same for the odd word at
  `f = ∞`, which has the class of the odd word at `f = 2`.
* `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt`: at `p = 2`, two
  classes with nondegenerate nonalternating degree-one forms are carried to one another by a
  continuous automorphism.
* `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo_zero_of_two`:
  the alternating case at `p = 2`, where the `p`-power part vanishes.
* `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd`,
  `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOddTop`,
  `TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven`: the
  nonalternating case at `p = 2`, of odd and of even rank.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Propositions 3 and 4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Theorem 3.9.19.
-/

public section

namespace TauCeti

open Subgroup Submodule
open scoped commutatorElement

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the linear maps
-- into `ZMod p` below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The `p`-power part of a class `ρ ∈ gr_1(F)`, as a functional on the continuous dual:
`χ ↦ Σ_i c_i χ(x_i)`, where `c_i` are the `p`-power coordinates of `ρ`. -/
private noncomputable def powerPartFunctional (ρ : gradedPiece p (freeProP p (Fin n)) 1) :
    continuousZModDual p (freeProP p (Fin n)) →ₗ[ZMod p] ZMod p :=
  ∑ i, (degreeOneBasis p (Fin n)).repr ρ (Sum.inl i) • (dualBasis p (Fin n)).coord i

private theorem powerPartFunctional_apply (ρ : gradedPiece p (freeProP p (Fin n)) 1)
    (χ : continuousZModDual p (freeProP p (Fin n))) :
    powerPartFunctional ρ χ =
      ∑ i, (degreeOneBasis p (Fin n)).repr ρ (Sum.inl i) * (χ.toMul (of i)).toAdd := by
  simp only [powerPartFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, dualBasis_repr, smul_eq_mul]

/-- The target class of the alternating case: `c • π ξ₁ + [ξ₁, ξ₂] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
private noncomputable def altClass (p n : ℕ) [Fact p.Prime] (c : ZMod p) :
    gradedPiece p (freeProP p (Fin n)) 1 :=
  c • gradedPow p _ 0 (gradedMkZero p _ (freeProPGen p n 0)) +
    ∑ a ∈ Finset.range (n / 2), gradedBracket p _ 0 0 (gradedMkZero p _ (freeProPGen p n (2 * a)))
      (gradedMkZero p _ (freeProPGen p n (2 * a + 1)))

private theorem altClass_repr_inl (c : ZMod p) (k : Fin n) :
    (degreeOneBasis p (Fin n)).repr (altClass p n c) (Sum.inl k) =
      if (k : ℕ) = 0 then c else 0 := by
  simp only [altClass, map_add, map_smul, map_sum, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, degreeOneBasis_repr_gradedBracket_inl, Finset.sum_const_zero,
    add_zero, degreeOneBasis_repr_gradedPow_gradedMkZero_inl, toMul_dualBasis_freeProPGen,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

private theorem gradedPow_gradedMkZero_freeProPGen_eq_degreeOneBasis {a : ℕ} (ha : a < n) :
    gradedPow p _ 0 (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n a)) =
      degreeOneBasis p (Fin n) (Sum.inl ⟨a, ha⟩) := by
  rw [freeProPGen_of_lt p ha, degreeOneBasis_apply, degreeOneFamily_inl]

private theorem gradedBracket_gradedMkZero_freeProPGen_eq_degreeOneBasis {a b : ℕ} (hab : a < b)
    (hb : b < n) :
    gradedBracket p _ 0 0 (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n a))
        (gradedMkZero p _ (freeProPGen p n b)) =
      degreeOneBasis p (Fin n) (Sum.inr ⟨(⟨a, hab.trans hb⟩, ⟨b, hb⟩), hab⟩) := by
  rw [freeProPGen_of_lt p (hab.trans hb), freeProPGen_of_lt p hb, degreeOneBasis_apply,
    degreeOneFamily_inr]

private theorem altClass_repr_inr (c : ZMod p) {i j : Fin n} (hij : i < j) :
    (degreeOneBasis p (Fin n)).repr (altClass p n c) (Sum.inr ⟨(i, j), hij⟩) =
      if (i : ℕ) % 2 = 0 ∧ (j : ℕ) = i + 1 then 1 else 0 := by
  have h0 : (degreeOneBasis p (Fin n)).repr
      (gradedPow p _ 0 (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n 0)))
      (Sum.inr ⟨(i, j), hij⟩) = 0 := by
    rw [gradedPow_gradedMkZero_freeProPGen_eq_degreeOneBasis i.pos, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (by simp)]
  have hsum : ∀ a ∈ Finset.range (n / 2),
      (degreeOneBasis p (Fin n)).repr (gradedBracket p _ 0 0
        (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * a)))
        (gradedMkZero p _ (freeProPGen p n (2 * a + 1)))) (Sum.inr ⟨(i, j), hij⟩) =
      if 2 * a = (i : ℕ) ∧ 2 * a + 1 = (j : ℕ) then 1 else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [gradedBracket_gradedMkZero_freeProPGen_eq_degreeOneBasis (Nat.lt_succ_self _) (by omega),
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [Fin.ext_iff]
  simp only [altClass, map_add, map_smul, map_sum, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, h0, smul_zero, zero_add, Finset.sum_congr rfl hsum]
  split_ifs with h
  · rw [Finset.sum_eq_single ((i : ℕ) / 2)]
    · rw [ite_eq_left (by omega)]
    · intro b _ hb
      rw [ite_eq_right (by omega)]
    · intro hi
      rw [Finset.mem_range] at hi
      omega
  · exact Finset.sum_eq_zero fun a _ ↦ ite_eq_right (by omega)

/-! ### Interleaving a symplectic basis -/

/-- The interleaving `Fin n → Fin m ⊕ Fin m` for `n = 2m`: an even index `2a` goes to `inr a` and
an odd index `2a + 1` to `inl a`, so that the pair `(2a, 2a + 1)` is a hyperbolic pair of the
standard symplectic matrix with `B (b (2a)) (b (2a + 1)) = 1`. -/
private def interleave {m : ℕ} (hn : n = 2 * m) (k : Fin n) : Fin m ⊕ Fin m :=
  if (k : ℕ) % 2 = 0 then Sum.inr ⟨k / 2, by omega⟩ else Sum.inl ⟨k / 2, by omega⟩

private theorem interleave_bijective {m : ℕ} (hn : n = 2 * m) :
    Function.Bijective (interleave hn) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun k l hkl ↦ ?_, by simp; omega⟩
  unfold interleave at hkl
  split_ifs at hkl with hk hl hl <;>
    simp only [Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at hkl <;> exact Fin.ext (by omega)

private theorem J_interleave {m : ℕ} (hn : n = 2 * m) {i j : Fin n} (hij : i < j) :
    Matrix.J (Fin m) (ZMod p) (interleave hn i) (interleave hn j) =
      if (i : ℕ) % 2 = 0 ∧ (j : ℕ) = i + 1 then 1 else 0 := by
  have hij' : (i : ℕ) < j := hij
  unfold interleave
  split_ifs with hi hj hj h h h h <;>
    simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Fin.ext_iff] <;> omega

private theorem interleave_eq_inr_zero_iff {m : ℕ} (hn : n = 2 * (m + 1)) (k : Fin n) :
    interleave hn k = Sum.inr 0 ↔ (k : ℕ) = 0 := by
  unfold interleave
  split_ifs with hk
  · simp only [Sum.inr.injEq, Fin.ext_iff, Fin.val_zero]
    omega
  · simp only [false_iff]
    omega

/-- **Realizing an interleaved symplectic basis by an automorphism.** Let `ρ ∈ gr_1(F)` have a
symplectic basis `b : Fin m ⊕ Fin m` for its degree-one form, with `n = 2m`, and suppose the
`p`-power part of `ρ` takes the value `c₀` on the vector of `b` at the interleaved position `0`
and vanishes on the others. Then some continuous automorphism of `F` carries `ρ` to
`c₀ • π ξ₁ + [ξ₁, ξ₂] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
private theorem exists_gradedMap_eq_altClass_of_basis (ρ : gradedPiece p (freeProP p (Fin n)) 1)
    {m : ℕ} (hn : n = 2 * m)
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod p) (continuousZModDual p (freeProP p (Fin n))))
    (hb : ∀ x y, degreeOneForm ρ (b x) (b y) = Matrix.J (Fin m) (ZMod p) x y) (c₀ : ZMod p)
    (hℓ : ∀ k : Fin n, powerPartFunctional ρ (b (interleave hn k)) =
      if (k : ℕ) = 0 then c₀ else 0) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ = altClass p n c₀ := by
  let σ : Fin n ≃ Fin m ⊕ Fin m := Equiv.ofBijective _ (interleave_bijective hn)
  let η := b.reindex σ.symm
  have hη (k : Fin n) : η k = b (interleave hn k) := by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    rfl
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_continuousZModDualMap_eq
      ((dualBasis p (Fin n)).equiv η (Equiv.refl _))
  refine ⟨e, ?_⟩
  have hed (k : Fin n) : (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuousZModDualMap
      (dualBasis p (Fin n) k) = b (interleave hn k) := by
    rw [he, Module.Basis.equiv_apply, Equiv.refl_apply, hη]
  rw [(degreeOneBasis p (Fin n)).ext_elem_iff]
  rintro (k | ⟨⟨i, j⟩, hij⟩)
  · rw [degreeOneBasis_repr_gradedMap_inl, altClass_repr_inl, ← hℓ k, powerPartFunctional_apply,
      hed]
  · rw [← degreeOneForm_dualBasis_of_lt _ hij, altClass_repr_inr, degreeOneForm_gradedMap,
      LinearMap.compl₁₂_apply, hed, hed, hb, J_interleave hn hij]


/-! ### The two alternating normal forms -/

private theorem gradedMk_demushkinWordNeTwo_zero_eq_altClass :
    gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo 0 n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one (dvd_zero p) n _⟩ = altClass p n 0 := by
  rw [gradedMk_demushkinWordNeTwo (dvd_zero p), altClass, Nat.zero_div, zero_smul, zero_smul]

private theorem gradedMk_demushkinWordNeTwo_self_eq_altClass :
    gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo p n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩ = altClass p n 1 := by
  rw [gradedMk_demushkinWordNeTwo dvd_rfl, altClass, Nat.div_self (Fact.out : p.Prime).pos,
    one_smul, one_smul]

/-- **The `p`-power coordinates of the class of the `q ≠ 2` normal-form word**
`x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`, for `p ∣ q`: the coefficient of `π ξ₁` is `q / p`, and the other
`p`-power coordinates vanish. -/
@[simp]
theorem degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl {q : ℕ} (hq : p ∣ q) (k : Fin n) :
    (degreeOneBasis p (Fin n)).repr (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) (Sum.inl k) =
      if (k : ℕ) = 0 then ((q / p : ℕ) : ZMod p) else 0 := by
  have hn : 0 < n := k.pos
  have h0 : gradedPow p (freeProP p (Fin n)) 0
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n 0)) =
      degreeOneBasis p (Fin n) (Sum.inl ⟨0, hn⟩) := by
    rw [degreeOneBasis_apply, degreeOneFamily_inl, freeProPGen_of_lt p hn]
  -- The bracket summands have no `p`-power coordinates.
  have hbr : (degreeOneBasis p (Fin n)).repr (∑ i ∈ Finset.range (n / 2),
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * i)))
        (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * i + 1)))) (Sum.inl k) = 0 := by
    rw [map_sum, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun i _ ↦ degreeOneBasis_repr_gradedBracket_inl _ _ _
  rw [gradedMk_demushkinWordNeTwo hq, map_add, Finsupp.add_apply, hbr, add_zero, h0, map_nsmul,
    Finsupp.smul_apply, Module.Basis.repr_self_apply]
  by_cases hk : (k : ℕ) = 0
  · obtain rfl : (⟨0, hn⟩ : Fin n) = k := Fin.ext hk.symm
    simp
  · simp [hk, Fin.ext_iff, Ne.symm hk]

private theorem even_of_basis {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod p) (continuousZModDual p (freeProP p (Fin n)))) :
    n = 2 * m := by
  have := Fintype.card_congr ((dualBasis p (Fin n)).indexEquiv b)
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

/-- The case of a vanishing `p`-power part: any symplectic basis will do. -/
private theorem exists_gradedMap_eq_altClass_zero (ρ : gradedPiece p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm ρ).Nondegenerate) (halt : (degreeOneForm ρ).IsAlt)
    (hℓ : powerPartFunctional ρ = 0) :
    Even n ∧ ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ = altClass p n 0 := by
  obtain ⟨m, b, hb⟩ := halt.exists_basis_toMatrix_eq_J hnd
  have hn := even_of_basis b
  refine ⟨⟨m, by omega⟩, exists_gradedMap_eq_altClass_of_basis ρ hn b
    (fun x y ↦ by rw [← hb, LinearMap.BilinForm.toMatrix_apply]) 0 fun k ↦ ?_⟩
  rw [hℓ, LinearMap.zero_apply, ite_self]

/-- The case of a nonvanishing `p`-power part `ℓ`: represent `ℓ` by a vector `θ` through the
form, complete `θ` to a hyperbolic pair `(θ, e₀)` and adjoin a symplectic basis of the orthogonal
complement, which lies in the kernel of `ℓ`. -/
private theorem exists_gradedMap_eq_altClass_one (ρ : gradedPiece p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm ρ).Nondegenerate) (halt : (degreeOneForm ρ).IsAlt)
    (hℓ : powerPartFunctional ρ ≠ 0) :
    Even n ∧ ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ = altClass p n 1 := by
  -- `θ` represents `ℓ`: `B χ θ = ℓ χ` for every `χ`.
  obtain ⟨θ, hθ⟩ : ∃ θ, ∀ χ, degreeOneForm ρ χ θ = powerPartFunctional ρ χ :=
    ⟨((degreeOneForm ρ).toDual hnd).symm (-powerPartFunctional ρ), fun χ ↦ by
      rw [← halt.neg_eq, LinearMap.BilinForm.apply_toDual_symm_apply, LinearMap.neg_apply,
        neg_neg]⟩
  have hθ0 : θ ≠ 0 := fun h ↦ hℓ (LinearMap.ext fun χ ↦ by
    rw [← hθ, h, map_zero, LinearMap.zero_apply])
  -- A partner `e₀` with `B e₀ θ = 1`.
  obtain ⟨e₀, hfe⟩ : ∃ e₀, degreeOneForm ρ e₀ θ = 1 := by
    obtain ⟨w, hw⟩ : ∃ w, degreeOneForm ρ w θ ≠ 0 := by
      by_contra! h
      exact hθ0 (hnd.2 θ h)
    exact ⟨(degreeOneForm ρ w θ)⁻¹ • w, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  -- A symplectic basis of the orthogonal complement of the hyperbolic pair.
  have hZalt : ((degreeOneForm ρ).restrict
      ((degreeOneForm ρ).orthogonal (span (ZMod p) {θ, e₀}))).IsAlt :=
    fun z ↦ halt.self_eq_zero z
  obtain ⟨m, c, hc⟩ :=
    hZalt.exists_basis_toMatrix_eq_J (halt.restrict_nondegenerate_orthogonal_span_pair hfe hnd)
  have hc' : ∀ x y, degreeOneForm ρ (c x) (c y) = Matrix.J (Fin m) (ZMod p) x y := fun x y ↦ by
    rw [← hc, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply]
  obtain ⟨b, hb, hbd⟩ :=
    halt.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
  have hn := even_of_basis b
  refine ⟨⟨m + 1, by omega⟩, exists_gradedMap_eq_altClass_of_basis ρ hn b hb 1 fun k ↦ ?_⟩
  -- `ℓ` vanishes on every vector of `b` except `e₀`, where it is `1`.
  have hZ : ∀ x, powerPartFunctional ρ (c x) = 0 := fun x ↦ by
    have h1 : degreeOneForm ρ θ (c x) = 0 :=
      ((LinearMap.BilinForm.mem_orthogonal_span_pair_iff (degreeOneForm ρ)).1 (c x).2).1
    rw [← hθ, ← halt.neg_eq, h1, neg_zero]
  have hℓb : ∀ x, powerPartFunctional ρ (b x) = if x = Sum.inr 0 then 1 else 0 := by
    rintro (x | x) <;> induction x using Fin.cases <;> rw [hbd]
    · simp only [Sum.elim_inl, Fin.cons_zero, ← hθ, halt.self_eq_zero]
      simp
    · simp only [Sum.elim_inl, Fin.cons_succ, hZ]
      simp
    · simp only [Sum.elim_inr, Fin.cons_zero, ← hθ, hfe]
      simp
    · simp only [Sum.elim_inr, Fin.cons_succ, hZ]
      simp [Fin.succ_ne_zero]
  rw [hℓb]
  simp only [interleave_eq_inr_zero_iff]

/-- **Labute's normal form modulo `λ_2`, the alternating case.** Let `F` be the free pro-`p`
group on `n` generators and let `ρ ∈ gr_1(F)` have nondegenerate alternating degree-one form,
which for odd `p` is every nondegenerate form. Then `n` is even, and a continuous automorphism of
`F` carries `ρ` to the class of `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` or to the class of
`x₁^p (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. For a relator `r` with class `ρ`, this is
`r ≡ x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n) mod λ_2(F)` after a change of basis, with `q = 0` or `q = p`;
every `q` with `p² ∣ q` gives the same class as `q = 0`. -/
theorem exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo
    (ρ : gradedPiece p (freeProP p (Fin n)) 1) (hnd : (degreeOneForm ρ).Nondegenerate)
    (halt : (degreeOneForm ρ).IsAlt) :
    Even n ∧ ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ =
        gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo 0 n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one (dvd_zero p) n _⟩ ∨
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ =
        gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo p n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩ := by
  by_cases hℓ : powerPartFunctional ρ = 0
  · obtain ⟨hn, e, he⟩ := exists_gradedMap_eq_altClass_zero ρ hnd halt hℓ
    exact ⟨hn, e, Or.inl (he.trans gradedMk_demushkinWordNeTwo_zero_eq_altClass.symm)⟩
  · obtain ⟨hn, e, he⟩ := exists_gradedMap_eq_altClass_one ρ hnd halt hℓ
    exact ⟨hn, e, Or.inr (he.trans gradedMk_demushkinWordNeTwo_self_eq_altClass.symm)⟩

/-- **Labute's normal form modulo `λ_2`, the alternating case at `p = 2`.** At `p = 2` the
diagonal of the degree-one form consists of the `2`-power coordinates, so an alternating form has
no `2`-power part and only the first alternative occurs: a continuous automorphism carries `ρ` to
the class of `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo_zero_of_two
    (hp : p = 2) (ρ : gradedPiece p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm ρ).Nondegenerate) (halt : (degreeOneForm ρ).IsAlt) :
    Even n ∧ ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ρ =
        gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo 0 n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one (dvd_zero p) n _⟩ := by
  have hℓ : powerPartFunctional ρ = 0 := by
    have hc (k : Fin n) : (degreeOneBasis p (Fin n)).repr ρ (Sum.inl k) = 0 := by
      have h := degreeOneForm_dualBasis_self ρ k
      rw [halt.self_eq_zero] at h
      subst hp
      rw [Nat.choose_self, one_nsmul] at h
      exact h.symm
    simp [powerPartFunctional, hc]
  obtain ⟨hn, e, he⟩ := exists_gradedMap_eq_altClass_zero ρ hnd halt hℓ
  exact ⟨hn, e, he.trans gradedMk_demushkinWordNeTwo_zero_eq_altClass.symm⟩


/-! ### The normal form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` is nondegenerate -/

/-- The value of the degree-one form of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` on a
character and the `j`-th coordinate character. -/
private theorem degreeOneForm_demushkinWordNeTwo_dualBasis {q : ℕ} (hq : p ∣ q)
    (χ : continuousZModDual p (freeProP p (Fin n))) (j : Fin n) :
    degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) χ (dualBasis p (Fin n) j) =
      (q / p) • p.choose 2 • (if (j : ℕ) = 0 then (χ.toMul (freeProPGen p n 0)).toAdd else 0) +
        ∑ a ∈ Finset.range (n / 2),
          ((if (j : ℕ) = 2 * a + 1 then (χ.toMul (freeProPGen p n (2 * a))).toAdd else 0) -
            if (j : ℕ) = 2 * a then (χ.toMul (freeProPGen p n (2 * a + 1))).toAdd else 0) := by
  rw [gradedMk_demushkinWordNeTwo hq]
  simp only [map_add, map_sum, map_nsmul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, degreeOneForm_gradedPow_gradedMkZero,
    degreeOneForm_gradedBracket_gradedMkZero, toMul_dualBasis_freeProPGen, mul_ite, mul_one,
    mul_zero]

/-- **The degree-one form of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` is nondegenerate for `n` even** and
`p ∣ q`: pairing with the `j`-th coordinate character reads off the value of a character at the
partner `x_{j±1}` of `x_j` in the commutator pairs, up to the `p`-power term, which involves only
the value at `x₁` and is read off first. This covers `q = 0`, and at `p = 2` also `q ≡ 2 mod 4`,
where the form is not alternating. -/
theorem nondegenerate_degreeOneForm_demushkinWordNeTwo (hn : Even n) {q : ℕ} (hq : p ∣ q) :
    (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1
      ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)).Nondegenerate := by
  obtain ⟨N, hN⟩ := hn
  refine ((isRefl_degreeOneForm (gradedMk p (freeProP p (Fin n)) 1
    ⟨demushkinWordNeTwo q n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)).nondegenerate_iff_separatingLeft).2
    fun χ hχ ↦ ?_
  rw [(dualBasis p (Fin n)).ext_elem_iff]
  intro i
  have hin := i.isLt
  rw [map_zero, Finsupp.zero_apply, dualBasis_repr, ← freeProPGen_val]
  have hχ' (j : ℕ) (hj : j < n) := hχ (dualBasis p (Fin n) ⟨j, hj⟩)
  simp only [degreeOneForm_demushkinWordNeTwo_dualBasis hq] at hχ'
  -- Pairing with the coordinate character at `x_{2a+2}` reads off the value at `x_{2a+1}`.
  have heven (a : ℕ) (ha : 2 * a < n) : (χ.toMul (freeProPGen p n (2 * a))).toAdd = 0 := by
    have h := hχ' (2 * a + 1) (by omega)
    rw [ite_eq_right (by omega), smul_zero, smul_zero, zero_add,
      Finset.sum_eq_single a (fun b _ hb ↦ by
        rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero])
      (fun ha' ↦ by rw [Finset.mem_range] at ha'; omega),
      ite_eq_left rfl, ite_eq_right (by omega), sub_zero] at h
    exact h
  -- Pairing with the coordinate character at `x_{2a+1}` reads off the value at `x_{2a+2}`, once
  -- the `p`-power term, which involves only the value at `x₁`, is known to vanish.
  have hodd (a : ℕ) (ha : 2 * a + 1 < n) :
      (χ.toMul (freeProPGen p n (2 * a + 1))).toAdd = 0 := by
    have h := hχ' (2 * a) (by omega)
    have h0 : (χ.toMul (freeProPGen p n 0)).toAdd = 0 := by simpa using heven 0 (by omega)
    rw [h0, ite_self, smul_zero, smul_zero, zero_add,
      Finset.sum_eq_single a (fun b _ hb ↦ by
        rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero])
      (fun ha' ↦ by rw [Finset.mem_range] at ha'; omega),
      ite_eq_right (by omega), ite_eq_left rfl, zero_sub, neg_eq_zero] at h
    exact h
  rcases Nat.even_or_odd (i : ℕ) with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha, ← two_mul]
    exact heven a (by omega)
  · rw [ha]
    exact hodd a (by omega)


/-! ### The dyadic nonalternating normal forms -/

section Two

variable (ρ : gradedPiece 2 (freeProP 2 (Fin n)) 1)

/-- **At `p = 2` the classes with nondegenerate nonalternating degree-one form form a single
orbit**: two such classes are carried to one another by a continuous automorphism of `F`. Such
forms are symmetric, any two of them on spaces of the same dimension are equivalent, and at
`p = 2` the form determines the class. -/
theorem exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt
    (T : gradedPiece 2 (freeProP 2 (Fin n)) 1)
    (hnd : (degreeOneForm ρ).Nondegenerate) (hnalt : ¬ (degreeOneForm ρ).IsAlt)
    (hTnd : (degreeOneForm T).Nondegenerate) (hTnalt : ¬ (degreeOneForm T).IsAlt) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
        (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ρ = T := by
  obtain ⟨φ⟩ := (isSymm_degreeOneForm_of_two rfl ρ).equivalent_of_finrank_eq
    (fun a ↦ isSquare_of_charTwo' a) hnd (fun h ↦ (hnalt h).elim)
    (isSymm_degreeOneForm_of_two rfl T) hTnd (fun h ↦ (hTnalt h).elim) rfl
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_degreeOneForm_gradedMap_dualBasis ρ
    ((dualBasis 2 (Fin n)).map φ.toLinearEquiv.symm)
  refine ⟨e, degreeOneForm_injective_of_two rfl
    (LinearMap.BilinForm.ext_basis (dualBasis 2 (Fin n)) fun i j ↦ ?_)⟩
  have hφ (x : continuousZModDual 2 (freeProP 2 (Fin n))) :
      φ (φ.toLinearEquiv.symm x) = x :=
    φ.toLinearEquiv.apply_symm_apply x
  rw [he, Module.Basis.map_apply, Module.Basis.map_apply, ← φ.map_app, hφ, hφ]

private theorem pos_of_not_isAlt (hnalt : ¬ (degreeOneForm ρ).IsAlt) : 0 < n := by
  by_contra h
  apply hnalt
  intro χ
  have : χ = 0 := by
    rw [(dualBasis 2 (Fin n)).ext_elem_iff]
    intro i
    exact absurd i.isLt (by omega)
  simp [this]

/-- The value of the degree-one form of the class of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` on a
character and the `j`-th coordinate character. -/
private theorem degreeOneForm_demushkinWordTwoOdd_dualBasis {f : ℕ} (hf : 0 < f)
    (χ : continuousZModDual 2 (freeProP 2 (Fin n))) (j : Fin n) :
    degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n _⟩) χ
      (dualBasis 2 (Fin n) j) =
      (if (j : ℕ) = 0 then (χ.toMul (freeProPGen 2 n 0)).toAdd else 0) +
        2 ^ (f - 1) • (if (j : ℕ) = 1 then (χ.toMul (freeProPGen 2 n 1)).toAdd else 0) +
        ∑ a ∈ Finset.range (n / 2),
          ((if (j : ℕ) = 2 * a + 2 then (χ.toMul (freeProPGen 2 n (2 * a + 1))).toAdd else 0) -
            if (j : ℕ) = 2 * a + 1 then (χ.toMul (freeProPGen 2 n (2 * a + 2))).toAdd else 0) := by
  rw [gradedMk_demushkinWordTwoOdd hf]
  simp only [map_add, map_sum, map_nsmul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, degreeOneForm_gradedPow_gradedMkZero,
    degreeOneForm_gradedBracket_gradedMkZero, toMul_dualBasis_freeProPGen, Nat.choose_self,
    one_smul, mul_ite, mul_one, mul_zero]

/-- **The `2`-power coordinates of the class of the `q = 2`, `n` odd normal-form word**
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`, for `f ≥ 1`: the coefficient of `π ξ₁` is `1`, that of
`π ξ₂` is `2^{f-1}`, and the other `2`-power coordinates vanish. -/
@[simp]
theorem degreeOneBasis_repr_gradedMk_demushkinWordTwoOdd_inl {f : ℕ} (hf : 0 < f) (k : Fin n) :
    (degreeOneBasis 2 (Fin n)).repr
      (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n _⟩)
      (Sum.inl k) =
      (if (k : ℕ) = 0 then 1 else 0) + 2 ^ (f - 1) • if (k : ℕ) = 1 then 1 else 0 := by
  rw [gradedMk_demushkinWordTwoOdd hf]
  simp only [map_add, map_sum, map_nsmul, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, degreeOneBasis_repr_gradedBracket_inl, Finset.sum_const_zero, add_zero,
    degreeOneBasis_repr_gradedPow_gradedMkZero_inl, toMul_dualBasis_freeProPGen]

/-- **The vanishing `2`-power coordinates of the odd dyadic normal-form word**, for `f ≥ 2`:
all coordinates except that of `x₁` vanish. -/
theorem degreeOneBasis_repr_gradedMk_demushkinWordTwoOdd_inl_eq_zero_iff {f : ℕ}
    (hf : 2 ≤ f) (k : Fin n) :
    (degreeOneBasis 2 (Fin n)).repr
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
          demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n _⟩)
        (Sum.inl k) = 0 ↔ (k : ℕ) ≠ 0 := by
  obtain ⟨g, hg⟩ : ∃ g, f - 1 = g + 1 := ⟨f - 2, by omega⟩
  rw [degreeOneBasis_repr_gradedMk_demushkinWordTwoOdd_inl (zero_lt_two.trans_le hf), hg,
    pow_succ, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, add_zero]
  simp

/-- **The degree-one form of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` is not alternating**, for
`n ≥ 1` and `f ≥ 1`: its value on the first coordinate character twice is `1`. -/
theorem not_isAlt_degreeOneForm_demushkinWordTwoOdd (hn : 0 < n) {f : ℕ} (hf : 0 < f) :
    ¬ (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n _⟩)).IsAlt := by
  intro h
  have := h (dualBasis 2 (Fin n) ⟨0, hn⟩)
  rw [degreeOneForm_dualBasis_self, degreeOneBasis_repr_gradedMk_demushkinWordTwoOdd_inl hf] at this
  simp at this

/-- **The first coordinate character splits off the degree-one form of
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`**, for `n ≥ 1` and `f ≥ 1`: pairing any character `χ` with
the first coordinate character reads off `χ(x₁)`, because `x₁` occurs in no commutator of the
word. In particular the first coordinate character is orthogonal to all the others. -/
theorem degreeOneForm_gradedMk_demushkinWordTwoOdd_dualBasis_zero (hn : 0 < n) {f : ℕ}
    (hf : 0 < f) (χ : continuousZModDual 2 (freeProP 2 (Fin n))) :
    degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n _⟩) χ
      (dualBasis 2 (Fin n) ⟨0, hn⟩) = (χ.toMul (freeProPGen 2 n 0)).toAdd := by
  rw [degreeOneForm_demushkinWordTwoOdd_dualBasis hf]
  simp

/-- **The degree-one form of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` is nondegenerate for `n`
odd and `f ≥ 1`**: pairing with the `j`-th coordinate character reads off the value of a character
at `x₁` for `j = 1`, and at the partner `x_{j±1}` of `x_j` in the commutator pairs otherwise (for
`j = 2` up to the diagonal term `2^{f-1} • χ(x₂)`, which vanishes once the value at `x₂` is read
off from `j = 3`). -/
theorem nondegenerate_degreeOneForm_demushkinWordTwoOdd (hn : Odd n) {f : ℕ} (hf : 0 < f) :
    (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n _⟩)).Nondegenerate := by
  obtain ⟨N, hN⟩ := hn
  refine ((isSymm_degreeOneForm_of_two rfl _).isRefl.nondegenerate_iff_separatingLeft).2
    fun χ hχ ↦ ?_
  rw [(dualBasis 2 (Fin n)).ext_elem_iff]
  intro i
  rw [map_zero, Finsupp.zero_apply, dualBasis_repr, ← freeProPGen_val]
  have hχ' (j : ℕ) (hj : j < n) := hχ (dualBasis 2 (Fin n) ⟨j, hj⟩)
  simp only [degreeOneForm_demushkinWordTwoOdd_dualBasis hf] at hχ'
  -- The value at `x₁`.
  have hc0 : (χ.toMul (freeProPGen 2 n 0)).toAdd = 0 := by
    rw [← degreeOneForm_gradedMk_demushkinWordTwoOdd_dualBasis_zero (by omega) hf χ]
    exact hχ _
  -- The value at `x_{j-1}` for `j ≥ 2` even is the pairing with the `j`-th coordinate character.
  have keyEven (j : ℕ) (hjn : j < n) (hj0 : j ≠ 0) (hj : j % 2 = 0) :
      (χ.toMul (freeProPGen 2 n (j - 1))).toAdd = 0 := by
    have h := hχ' j hjn
    rw [ite_eq_right hj0, ite_eq_right (by omega), smul_zero, add_zero, zero_add,
      Finset.sum_eq_single (j / 2 - 1), ite_eq_left (by omega), ite_eq_right (by omega),
      sub_zero] at h
    · convert h using 4
      omega
    · intro b _ hb
      rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    · intro hj'
      rw [Finset.mem_range] at hj'
      omega
  -- The value at `x_{j+1}` for `j` odd is the pairing with the `j`-th coordinate character.
  have keyOdd (j : ℕ) (hjn : j < n) (hj : j % 2 = 1) :
      (χ.toMul (freeProPGen 2 n (j + 1))).toAdd = 0 := by
    have h := hχ' j hjn
    have h1 : (if j = 1 then (χ.toMul (freeProPGen 2 n 1)).toAdd else 0) = 0 := by
      split_ifs with h1
      · exact keyEven 2 (by omega) (by omega) (by omega)
      · rfl
    rw [ite_eq_right (by omega), h1, smul_zero, add_zero, zero_add,
      Finset.sum_eq_single (j / 2), ite_eq_right (by omega), ite_eq_left (by omega), zero_sub,
      neg_eq_zero] at h
    · convert h using 4
      omega
    · intro b _ hb
      rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    · intro hj'
      rw [Finset.mem_range] at hj'
      omega
  have hin := i.isLt
  rcases eq_or_ne (i : ℕ) 0 with h0 | h0
  · rw [h0]
    exact hc0
  rcases Nat.even_or_odd (i : ℕ) with hi | hi
  · obtain ⟨r, hr⟩ := hi
    have := keyOdd ((i : ℕ) - 1) (by omega) (by omega)
    -- The predecessor of `i` is an odd index whose successor is `i`.
    have h3 : (i : ℕ) - 1 + 1 = i := by omega
    rwa [h3] at this
  · obtain ⟨r, hr⟩ := hi
    have := keyEven ((i : ℕ) + 1) (by omega) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this

/-- The value of the degree-one form of the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` on a character and the `j`-th coordinate
character. -/
private theorem degreeOneForm_demushkinWordTwoEven_dualBasis {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f)
    (χ : continuousZModDual 2 (freeProP 2 (Fin n))) (j : Fin n) :
    degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha hf n _⟩) χ (dualBasis 2 (Fin n) j) =
      (1 + a / 2) • (if (j : ℕ) = 0 then (χ.toMul (freeProPGen 2 n 0)).toAdd else 0) +
        ((if (j : ℕ) = 1 then (χ.toMul (freeProPGen 2 n 0)).toAdd else 0) -
          if (j : ℕ) = 0 then (χ.toMul (freeProPGen 2 n 1)).toAdd else 0) +
        2 ^ (f - 1) • (if (j : ℕ) = 2 then (χ.toMul (freeProPGen 2 n 2)).toAdd else 0) +
        ∑ i ∈ Finset.range (n / 2 - 1),
          ((if (j : ℕ) = 2 * i + 3 then (χ.toMul (freeProPGen 2 n (2 * i + 2))).toAdd else 0) -
            if (j : ℕ) = 2 * i + 2 then (χ.toMul (freeProPGen 2 n (2 * i + 3))).toAdd else 0) := by
  rw [gradedMk_demushkinWordTwoEven ha hf]
  simp only [map_add, map_sum, map_nsmul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, degreeOneForm_gradedPow_gradedMkZero,
    degreeOneForm_gradedBracket_gradedMkZero, toMul_dualBasis_freeProPGen, Nat.choose_self,
    one_smul, mul_ite, mul_one, mul_zero]

private theorem degreeOneBasis_repr_demushkinWordTwoEven_inl {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f)
    (k : Fin n) :
    (degreeOneBasis 2 (Fin n)).repr
      (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha hf n _⟩) (Sum.inl k) =
      (1 + a / 2) • (if (k : ℕ) = 0 then 1 else 0) +
        2 ^ (f - 1) • if (k : ℕ) = 2 then 1 else 0 := by
  rw [gradedMk_demushkinWordTwoEven ha hf]
  simp only [map_add, map_sum, map_nsmul, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, degreeOneBasis_repr_gradedBracket_inl, Finset.sum_const_zero, add_zero,
    degreeOneBasis_repr_gradedPow_gradedMkZero_inl, toMul_dualBasis_freeProPGen]

/-- **The degree-one form of `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` is not
alternating**, for `n ≥ 1`, `4 ∣ a` and `f ≥ 2`: its value on the first coordinate character twice
is `1`. (For `a ≡ 2 mod 4` and `f ≥ 2` the form is alternating.) -/
theorem not_isAlt_degreeOneForm_demushkinWordTwoEven (hn : 0 < n) {a f : ℕ} (ha : 4 ∣ a)
    (hf : 2 ≤ f) :
    ¬ (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
        demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_trans (Dvd.intro 2 rfl) ha)
          (zero_lt_two.trans_le hf) n _⟩)).IsAlt := by
  intro h
  have := h (dualBasis 2 (Fin n) ⟨0, hn⟩)
  rw [degreeOneForm_dualBasis_self, degreeOneBasis_repr_demushkinWordTwoEven_inl
    (dvd_trans (Dvd.intro 2 rfl) ha) (zero_lt_two.trans_le hf)] at this
  obtain ⟨b, rfl⟩ := ha
  have hb : 4 * b / 2 = 2 * b := by omega
  simp [hb, nsmul_eq_mul, CharTwo.two_eq_zero] at this

/-- **The degree-one form of `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` is nondegenerate
for `n` even, `a` even and `f ≥ 1`**: pairing with the second coordinate character reads off the
value of a character at `x₁`, pairing with the first one then reads off its value at `x₂`, and the
remaining coordinate characters read off the values at the partners in the commutator pairs (for
`j = 3` up to the diagonal term `2^{f-1} • χ(x₃)`, which vanishes once the value at `x₃` is read
off from `j = 4`). -/
theorem nondegenerate_degreeOneForm_demushkinWordTwoEven (hn : Even n) {a f : ℕ} (ha : 2 ∣ a)
    (hf : 0 < f) :
    (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha hf n _⟩)).Nondegenerate := by
  obtain ⟨N, hN⟩ := hn
  refine ((isSymm_degreeOneForm_of_two rfl _).isRefl.nondegenerate_iff_separatingLeft).2
    fun χ hχ ↦ ?_
  rw [(dualBasis 2 (Fin n)).ext_elem_iff]
  intro i
  have hn0 : 0 < n := i.pos
  rw [map_zero, Finsupp.zero_apply, dualBasis_repr, ← freeProPGen_val]
  have hχ' (j : ℕ) (hj : j < n) := hχ (dualBasis 2 (Fin n) ⟨j, hj⟩)
  simp only [degreeOneForm_demushkinWordTwoEven_dualBasis ha hf] at hχ'
  -- The values at `x₁` and `x₂`.
  have hc0 : (χ.toMul (freeProPGen 2 n 0)).toAdd = 0 := by
    have h := hχ' 1 (by omega)
    rw [ite_eq_right (by omega), smul_zero, ite_eq_left rfl, ite_eq_right (by omega), sub_zero,
      zero_add, ite_eq_right (by omega), smul_zero, add_zero,
      Finset.sum_eq_zero fun b _ ↦ by
        rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero], add_zero] at h
    exact h
  have hc1 : (χ.toMul (freeProPGen 2 n 1)).toAdd = 0 := by
    have h := hχ' 0 hn0
    rw [ite_eq_left rfl, hc0, smul_zero, ite_eq_right (by omega), ite_eq_left rfl, zero_sub,
      zero_add, ite_eq_right (by omega), smul_zero, add_zero,
      Finset.sum_eq_zero fun b _ ↦ by
        rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero], add_zero,
      neg_eq_zero] at h
    exact h
  -- The value at `x_{j-1}` for `j ≥ 3` odd is the pairing with the `j`-th coordinate character.
  have keyOdd (j : ℕ) (hjn : j < n) (hj2 : 2 ≤ j) (hj : j % 2 = 1) :
      (χ.toMul (freeProPGen 2 n (j - 1))).toAdd = 0 := by
    have h := hχ' j hjn
    rw [ite_eq_right (by omega), smul_zero, ite_eq_right (by omega), ite_eq_right (by omega),
      sub_zero, ite_eq_right (by omega), smul_zero, add_zero, add_zero, zero_add,
      Finset.sum_eq_single (j / 2 - 1), ite_eq_left (by omega), ite_eq_right (by omega),
      sub_zero] at h
    · convert h using 4
      omega
    · intro b _ hb
      rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    · intro hj'
      rw [Finset.mem_range] at hj'
      omega
  -- The value at `x_{j+1}` for `j ≥ 2` even is the pairing with the `j`-th coordinate character.
  have keyEven (j : ℕ) (hjn : j < n) (hj2 : 2 ≤ j) (hj : j % 2 = 0) :
      (χ.toMul (freeProPGen 2 n (j + 1))).toAdd = 0 := by
    have h := hχ' j hjn
    have h2 : (if j = 2 then (χ.toMul (freeProPGen 2 n 2)).toAdd else 0) = 0 := by
      split_ifs with h2
      · exact keyOdd 3 (by omega) (by omega) (by omega)
      · rfl
    rw [ite_eq_right (by omega), smul_zero, ite_eq_right (by omega), ite_eq_right (by omega),
      sub_zero, h2, smul_zero, add_zero, add_zero, zero_add,
      Finset.sum_eq_single (j / 2 - 1), ite_eq_right (by omega), ite_eq_left (by omega),
      zero_sub, neg_eq_zero] at h
    · convert h using 4
      omega
    · intro b _ hb
      rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    · intro hj'
      rw [Finset.mem_range] at hj'
      omega
  have hin := i.isLt
  rcases eq_or_ne (i : ℕ) 0 with h0 | h0
  · rw [h0]
    exact hc0
  rcases eq_or_ne (i : ℕ) 1 with h1 | h1
  · rw [h1]
    exact hc1
  rcases Nat.even_or_odd (i : ℕ) with hi | hi
  · obtain ⟨r, hr⟩ := hi
    have := keyOdd ((i : ℕ) + 1) (by omega) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this
  · obtain ⟨r, hr⟩ := hi
    have := keyEven ((i : ℕ) - 1) (by omega) (by omega) (by omega)
    -- The predecessor of `i` is an even index whose successor is `i`.
    have h3 : (i : ℕ) - 1 + 1 = i := by omega
    rwa [h3] at this

/-- **Labute's normal form modulo `λ_2`, the nonalternating case of odd rank.** Let `F` be the
free pro-`2` group on `n` generators, `n` odd, and let `ρ ∈ gr_1(F)` have nondegenerate degree-one
form that is not alternating. Then for every `f ≥ 2` a continuous automorphism of `F` carries `ρ`
to the class of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`, which is the class of
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd
    (hnd : (degreeOneForm ρ).Nondegenerate) (hnalt : ¬ (degreeOneForm ρ).IsAlt) (hn : Odd n)
    {f : ℕ} (hf : 2 ≤ f) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
          (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ρ =
        gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
          demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n _⟩ :=
  exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt ρ _ hnd hnalt
    (nondegenerate_degreeOneForm_demushkinWordTwoOdd hn (zero_lt_two.trans_le hf))
    (not_isAlt_degreeOneForm_demushkinWordTwoOdd hn.pos (zero_lt_two.trans_le hf))

/-- **The degree-one form of `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` is not alternating**, for `n ≥ 1`:
the word has the class of `x₁² x₂⁴ (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem not_isAlt_degreeOneForm_demushkinWordTwoOddTop (hn : 0 < n) :
    ¬ (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOddTop n (freeProPGen 2 n),
        demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n _⟩)).IsAlt := by
  rw [← gradedMk_demushkinWordTwoOdd_eq_gradedMk_demushkinWordTwoOddTop (f := 2) le_rfl]
  exact not_isAlt_degreeOneForm_demushkinWordTwoOdd hn two_pos

/-- **The degree-one form of `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` is nondegenerate for `n` odd**: the
word has the class of `x₁² x₂⁴ (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem nondegenerate_degreeOneForm_demushkinWordTwoOddTop (hn : Odd n) :
    (degreeOneForm (gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordTwoOddTop n (freeProPGen 2 n),
        demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n _⟩)).Nondegenerate := by
  rw [← gradedMk_demushkinWordTwoOdd_eq_gradedMk_demushkinWordTwoOddTop (f := 2) le_rfl]
  exact nondegenerate_degreeOneForm_demushkinWordTwoOdd hn two_pos

/-- **Labute's normal form modulo `λ_2`, the nonalternating case of odd rank, at level
`f = ∞`.** Let `F` be the free pro-`2` group on `n` generators, `n` odd, and let `ρ ∈ gr_1(F)`
have nondegenerate degree-one form that is not alternating. Then a continuous automorphism of `F`
carries `ρ` to the class of `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOddTop
    (hnd : (degreeOneForm ρ).Nondegenerate) (hnalt : ¬ (degreeOneForm ρ).IsAlt) (hn : Odd n) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
          (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ρ =
        gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOddTop n (freeProPGen 2 n),
          demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n _⟩ :=
  exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt ρ _ hnd hnalt
    (nondegenerate_degreeOneForm_demushkinWordTwoOddTop hn)
    (not_isAlt_degreeOneForm_demushkinWordTwoOddTop hn.pos)

/-- **Labute's normal form modulo `λ_2`, the nonalternating case of even rank.** Let `F` be the
free pro-`2` group on `n` generators, `n` even, and let `ρ ∈ gr_1(F)` have nondegenerate degree-one
form that is not alternating. Then for every `a` divisible by `4` and every `f ≥ 2` a continuous
automorphism of `F` carries `ρ` to the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, which is the class of
`x₁² (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven
    (hnd : (degreeOneForm ρ).Nondegenerate) (hnalt : ¬ (degreeOneForm ρ).IsAlt) (hn : Even n)
    {a f : ℕ} (ha : 4 ∣ a) (hf : 2 ≤ f) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
          (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ρ =
        gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
          demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_trans (Dvd.intro 2 rfl) ha)
            (zero_lt_two.trans_le hf) n _⟩ :=
  exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt ρ _ hnd hnalt
    (nondegenerate_degreeOneForm_demushkinWordTwoEven hn (dvd_trans (Dvd.intro 2 rfl) ha)
      (zero_lt_two.trans_le hf))
    (not_isAlt_degreeOneForm_demushkinWordTwoEven (pos_of_not_isAlt ρ hnalt) ha hf)


end Two


end freeProP

end TauCeti
