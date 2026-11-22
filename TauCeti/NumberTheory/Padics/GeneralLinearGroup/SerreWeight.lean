/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Unitriangular
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Serre weights of `GL₂(ℤ_ℓ)`

Let `ℓ` be a prime and `k` a field of characteristic `ℓ`. For `n : ℕ` and `m : ℤ`, the Serre
weight `σ_{n,m} = Sym^n k² ⊗ det^m` is the representation of `GL₂(ℤ_ℓ)` on the binary forms of
degree `n` over `k` obtained by reducing modulo `ℓ`: a matrix `g` acts through its image `r(g)`
in `GL₂(𝔽_ℓ) ⊆ GL₂(k)`, by the substitution of standard vectors `TauCeti.polynomialAction`
twisted by `det(r(g))^m` (`TauCeti.serreWeight`). The forms of degree `n` are `Sym^n k²` with its
induced action (`TauCeti.symPowerRepEquivPolynomialRep`), and they have dimension `n + 1`
(`TauCeti.finrank_homogeneousSubmodule_fin_two`); in particular `σ_{0,m}` is the character
`det^m` and `σ_{ℓ-1,0}` has dimension `ℓ`.

For `0 ≤ n ≤ ℓ - 1` and `m` modulo `ℓ - 1`, the `ℓ (ℓ - 1)` representations `σ_{n,m}` are the
irreducible smooth representations of `GL₂(ℤ_ℓ)` over an algebraic closure of `𝔽_ℓ` (BCDT, §1.3).
They are the weights from which the mod `ℓ` representations of `GL₂(ℚ_ℓ)` are compactly induced.
This file constructs them and proves:

* they factor through `GL₂(𝔽_ℓ)`: the first congruence subgroup, the kernel of reduction modulo
  `ℓ`, acts trivially (`TauCeti.serreWeight_apply_eq_one`);
* `σ_{n,m}` only depends on `m` modulo `ℓ - 1`, because `det(r(g))` lies in `𝔽_ℓ^×`
  (`TauCeti.serreWeight_eq_of_modEq`);
* `σ_{n,m}` is absolutely irreducible for `n < ℓ`: it is irreducible over every field of
  characteristic `ℓ` (`TauCeti.isIrreducible_serreWeight`). The images of the unitriangular
  matrices with parameters `0, …, n` in `SL₂(𝔽_ℓ)` already act irreducibly
  (`TauCeti.isIrreducible_polynomialRep_comp_map`);
* for `n, n' < ℓ`, `σ_{n,m} ≅ σ_{n',m'}` exactly when `n = n'` and `m ≡ m' [ZMOD ℓ - 1]`
  (`TauCeti.nonempty_equiv_serreWeight_iff`), so the `ℓ (ℓ - 1)` weights are pairwise
  non-isomorphic.

That every irreducible smooth representation is some `σ_{n,m}` is not proved here.

## Main definitions

* `TauCeti.serreWeight ℓ k n m`: the Serre weight `σ_{n,m} = Sym^n k² ⊗ det^m` of `GL₂(ℤ_ℓ)`.

## Main results

* `TauCeti.serreWeight_def`: `σ_{n,m}` is the twist by `det^m` of the binary forms of degree `n`.
* `TauCeti.coe_serreWeight_apply`: `g` acts by `det(r(g))^m` times the substitution of standard
  vectors by `r(g)`.
* `TauCeti.serreWeight_apply_eq_one`: the kernel of reduction modulo `ℓ` acts trivially.
* `TauCeti.serreWeight_eq_of_modEq`: `σ_{n,m} = σ_{n,m'}` when `m ≡ m' [ZMOD ℓ - 1]`.
* `TauCeti.isIrreducible_serreWeight`: `σ_{n,m}` is irreducible for `n < ℓ`.
* `TauCeti.nonempty_equiv_serreWeight_iff`: for `n < ℓ`, `σ_{n,m} ≅ σ_{n',m'}` if and only if
  `n = n'` and `m ≡ m' [ZMOD ℓ - 1]`.

## References

* C. Breuil, B. Conrad, F. Diamond and R. Taylor, *On the modularity of elliptic curves over `ℚ`:
  wild 3-adic exercises*, J. Amer. Math. Soc. 14 (2001), §1.3, p. 854: the irreducible
  representations `σ_{n,m}` of `GL₂(ℤ_ℓ)`.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ]

/-- **The Serre weight `σ_{n,m} = Sym^n k² ⊗ det^m` of `GL₂(ℤ_ℓ)`**, for a field `k` of
characteristic `ℓ`. A matrix `g` acts on the binary forms of degree `n` over `k` through its
reduction `r(g)` modulo `ℓ`, by `det(r(g))^m` times the substitution of standard vectors by
`r(g)`. -/
noncomputable def serreWeight (n : ℕ) (m : ℤ) :
    Representation k (GL (Fin 2) ℤ_[ℓ]) (homogeneousSubmodule (Fin 2) k n) :=
  Representation.charTwist
    ((GeneralLinearGroup.det ^ m).comp ((GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)).comp
      (GeneralLinearGroup.map PadicInt.toZMod)))
    ((polynomialRep (Fin 2) k n).comp ((GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)).comp
      (GeneralLinearGroup.map PadicInt.toZMod)))

/-- The defining equation of `TauCeti.serreWeight`: it is the twist of the binary forms of degree
`n`, on which `GL₂(ℤ_ℓ)` acts through reduction modulo `ℓ`, by the character `det^m` of the
reduction. This is how the general theory of `Representation.charTwist` applies to it. -/
theorem serreWeight_def (n : ℕ) (m : ℤ) :
    serreWeight ℓ k n m = Representation.charTwist
      ((GeneralLinearGroup.det ^ m).comp ((GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)).comp
        (GeneralLinearGroup.map PadicInt.toZMod)))
      ((polynomialRep (Fin 2) k n).comp ((GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)).comp
        (GeneralLinearGroup.map PadicInt.toZMod))) :=
  (rfl)

variable {ℓ k}

/-- **The action of `GL₂(ℤ_ℓ)` on a Serre weight**: with `r(g) ∈ GL₂(k)` the reduction of `g`
modulo `ℓ`, `g` sends a form `f(x, y)` of degree `n` to
`det(r(g))^m f(r(g)₀₀ x + r(g)₁₀ y, r(g)₀₁ x + r(g)₁₁ y)`. -/
@[simp]
theorem coe_serreWeight_apply {n : ℕ} {m : ℤ} (g : GL (Fin 2) ℤ_[ℓ])
    (f : homogeneousSubmodule (Fin 2) k n) :
    (serreWeight ℓ k n m g f : MvPolynomial (Fin 2) k) =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)
          (GeneralLinearGroup.map PadicInt.toZMod g)) ^ m : kˣ) : k) •
        polynomialAction (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)
          (GeneralLinearGroup.map PadicInt.toZMod g) : Matrix (Fin 2) (Fin 2) k) f := by
  simp [serreWeight_def]

/-- **Serre weights factor through `GL₂(𝔽_ℓ)`**: a matrix congruent to the identity modulo `ℓ`
acts trivially. -/
theorem serreWeight_apply_eq_one {n : ℕ} {m : ℤ} {g : GL (Fin 2) ℤ_[ℓ]}
    (hg : GeneralLinearGroup.map PadicInt.toZMod g = 1) : serreWeight ℓ k n m g = 1 := by
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  simp [hg]

/-- **A Serre weight only depends on the determinant exponent modulo `ℓ - 1`**: the reduction of
`det g` lies in `𝔽_ℓ^×`, whose elements have order dividing `ℓ - 1`. -/
theorem serreWeight_eq_of_modEq {n : ℕ} {m m' : ℤ} (h : m ≡ m' [ZMOD (ℓ - 1 : ℕ)]) :
    serreWeight ℓ k n m = serreWeight ℓ k n m' := by
  refine MonoidHom.ext fun g ↦ LinearMap.ext fun f ↦ Subtype.ext ?_
  rw [coe_serreWeight_apply, coe_serreWeight_apply, GeneralLinearGroup.map_det]
  congr 2
  -- The determinant of the reduction of `g` is a unit of `𝔽_ℓ`, so its powers are periodic.
  have hu : Units.map (ZMod.castHom dvd_rfl k : ZMod ℓ →* k)
      (GeneralLinearGroup.det (GeneralLinearGroup.map PadicInt.toZMod g)) ^ (ℓ - 1) = 1 := by
    rw [← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  rw [zpow_eq_zpow_emod' m hu, zpow_eq_zpow_emod' m' hu, h.eq]

/-- **Serre weights are irreducible**: for `n < ℓ`, the Serre weight `σ_{n,m}` is an irreducible
representation of `GL₂(ℤ_ℓ)` over every field `k` of characteristic `ℓ`. -/
theorem isIrreducible_serreWeight {n : ℕ} (hn : n < ℓ) (m : ℤ) :
    (serreWeight ℓ k n m).IsIrreducible := by
  rw [serreWeight_def, Representation.isIrreducible_charTwist_iff,
    ← GeneralLinearGroup.map_comp]
  refine isIrreducible_polynomialRep_comp_map _ fun h ↦ ?_
  rw [CharP.cast_eq_zero_iff k ℓ, Nat.Prime.dvd_factorial Fact.out] at h
  omega

/-- A matrix reducing to an upper unitriangular matrix acts on a Serre weight by the substitution
of standard vectors alone: its determinant twist is trivial. -/
private theorem coe_serreWeight_apply_of_map_eq_transvection {n : ℕ} {m : ℤ}
    {g : GL (Fin 2) ℤ_[ℓ]} {t : k}
    (hg : (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k) (GeneralLinearGroup.map PadicInt.toZMod
      g) : Matrix (Fin 2) (Fin 2) k) = transvection 0 1 t) (f : homogeneousSubmodule (Fin 2) k n) :
    (serreWeight ℓ k n m g f : MvPolynomial (Fin 2) k) =
      polynomialAction (transvection (0 : Fin 2) 1 t) f := by
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)
      (GeneralLinearGroup.map PadicInt.toZMod g)) = 1 := Units.ext <| by
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ (by decide), Units.val_one]
  rw [coe_serreWeight_apply, hdet, _root_.one_zpow, Units.val_one, one_smul, hg]

/-- A matrix reducing to `diag(u, 1)` scales a multiple of `xⁿ` in the Serre weight `σ_{n,m}` by
`u^m uⁿ`. -/
private theorem coe_serreWeight_apply_of_map_eq_diagonal {n : ℕ} {m : ℤ} {g : GL (Fin 2) ℤ_[ℓ]}
    {u : kˣ} (hg : (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k) (GeneralLinearGroup.map
      PadicInt.toZMod g) : Matrix (Fin 2) (Fin 2) k) = diagonal ![(u : k), 1])
    {f : homogeneousSubmodule (Fin 2) k n} {c : k}
    (hf : (f : MvPolynomial (Fin 2) k) = c • X 0 ^ n) :
    serreWeight ℓ k n m g f = (((u ^ m : kˣ) : k) * (u : k) ^ n) • f := by
  refine Subtype.ext ?_
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k)
      (GeneralLinearGroup.map PadicInt.toZMod g)) = u := Units.ext <| by
    simp [GeneralLinearGroup.val_det_apply, hg]
  have hx := polynomialAction_diagonal_polynomialMonomial k n 0 ![(u : k), 1]
  rw [polynomialMonomial_zero_right] at hx
  rw [coe_serreWeight_apply, hdet, hg, Submodule.coe_smul, hf, map_smul, hx]
  simp [smul_smul, mul_comm, mul_left_comm]

/-- **The determinant exponent of a Serre weight is determined modulo `ℓ - 1`.** For `n < ℓ`, a
linear automorphism of the forms of degree `n` intertwining `σ_{n,m}` with `σ_{n,m'}` forces
`m ≡ m' [ZMOD ℓ - 1]`. It carries the line of `xⁿ`, the vectors fixed by the upper unitriangular
matrices, to itself, and `diag(a, 1)` acts on that line by `aᵐ⁺ⁿ` on one side and by `aᵐ'⁺ⁿ` on the
other; taking `a` reducing to a generator of `𝔽_ℓ^×` gives the congruence. -/
private theorem modEq_of_linearEquiv {n : ℕ} (hn : n < ℓ) {m m' : ℤ}
    (F : homogeneousSubmodule (Fin 2) k n ≃ₗ[k] homogeneousSubmodule (Fin 2) k n)
    (hF : ∀ g v, F (serreWeight ℓ k n m g v) = serreWeight ℓ k n m' g (F v)) :
    m ≡ m' [ZMOD (ℓ - 1 : ℕ)] := by
  set v₀ : homogeneousSubmodule (Fin 2) k n := ⟨X 0 ^ n, isHomogeneous_X_pow 0 n⟩
  have hv₀ : F v₀ ≠ 0 := (map_ne_zero_iff F F.injective).mpr fun h ↦
    pow_ne_zero n (X_ne_zero (0 : Fin 2)) (congrArg Subtype.val h)
  -- `F v₀` is fixed by the lifts of the upper unitriangular matrices with parameters `0, …, n`, so
  -- it is a multiple of `xⁿ`.
  obtain ⟨c, hc⟩ : ∃ c : k, (F v₀ : MvPolynomial (Fin 2) k) = c • X 0 ^ n := by
    refine exists_eq_smul_X_zero_pow_of_polynomialAction_transvection_eq
      (x := fun j : Fin (n + 1) ↦ (j : k)) (fun a b hab ↦ Fin.ext ?_)
      (F v₀).property fun j ↦ ?_
    · exact ((CharP.natCast_eq_natCast k ℓ).mp hab).eq_of_lt_of_lt (by omega) (by omega)
    set g : GL (Fin 2) ℤ_[ℓ] := transvectionUnit (i := 0) (j := 1) (by decide) (j : ℤ_[ℓ])
    have hg : (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k) (GeneralLinearGroup.map
        PadicInt.toZMod g) : Matrix (Fin 2) (Fin 2) k) = transvection 0 1 (j : k) := by
      simp [g]
    have hfix : serreWeight ℓ k n m g v₀ = v₀ := Subtype.ext <| by
      simp [v₀, coe_serreWeight_apply_of_map_eq_transvection hg, transvection, Matrix.one_apply]
    rw [← coe_serreWeight_apply_of_map_eq_transvection (m := m') hg, ← hF, hfix]
  -- A matrix reducing to `diag(a, 1)`, with `a` reducing to a generator `a₀` of `𝔽_ℓ^×`.
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  set r := (a₀ : ZMod ℓ).val
  have hr : ((r : ℕ) : ZMod ℓ) = a₀ := ZMod.natCast_zmod_val _
  have hru : IsUnit ((r : ℕ) : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr <|
    PadicInt.norm_natCast_eq_one_iff.mpr ((ZMod.isUnit_iff_coprime r ℓ).mp (hr ▸ a₀.isUnit)).symm
  set u : kˣ := Units.map (ZMod.castHom dvd_rfl k : ZMod ℓ →* k) a₀
  set g := GeneralLinearGroup.mk'' (diagonal ![((r : ℕ) : ℤ_[ℓ]), 1]) (by simpa using hru)
  have hg : (GeneralLinearGroup.map (ZMod.castHom dvd_rfl k) (GeneralLinearGroup.map
      PadicInt.toZMod g) : Matrix (Fin 2) (Fin 2) k) = diagonal ![(u : k), 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [g, u, GeneralLinearGroup.map_apply, ← hr]
  -- Comparing the two eigenvalues of `g` on the line of `F v₀`.
  have hcomp := hF g v₀
  rw [coe_serreWeight_apply_of_map_eq_diagonal hg (c := 1) (one_smul k _).symm, map_smul,
    coe_serreWeight_apply_of_map_eq_diagonal hg hc] at hcomp
  have hu : u ^ m = u ^ m' := Units.ext <|
    mul_right_cancel₀ (pow_ne_zero n u.ne_zero) (smul_left_injective k hv₀ hcomp)
  rw [← map_zpow, ← map_zpow] at hu
  have hord : orderOf a₀ = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha₀, Nat.card_eq_fintype_card, ZMod.card_units]
  exact hord ▸ zpow_eq_zpow_iff_modEq.mp (Units.map_injective (ZMod.castHom dvd_rfl k).injective hu)

/-- **Classification of isomorphisms between Serre weights**: for `n < ℓ`, the Serre weights
`σ_{n,m}` and `σ_{n',m'}` are isomorphic exactly when `n = n'` and `m ≡ m' [ZMOD ℓ - 1]`. Thus
`σ_{n,m}` for `0 ≤ n ≤ ℓ - 1` and `m` modulo `ℓ - 1` are `ℓ (ℓ - 1)` pairwise non-isomorphic
irreducible representations of `GL₂(ℤ_ℓ)`. -/
theorem nonempty_equiv_serreWeight_iff {n n' : ℕ} (hn : n < ℓ) {m m' : ℤ} :
    Nonempty (Representation.Equiv (serreWeight ℓ k n m) (serreWeight ℓ k n' m')) ↔
      n = n' ∧ m ≡ m' [ZMOD (ℓ - 1 : ℕ)] := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨hnn, h⟩ ↦ ?_⟩
  · -- The dimensions `n + 1` and `n' + 1` agree.
    have hnn : n = n' := by
      simpa [finrank_homogeneousSubmodule_fin_two] using e.toLinearEquiv.finrank_eq
    subst hnn
    exact ⟨rfl, modEq_of_linearEquiv hn e.toLinearEquiv e.toIntertwiningMap.isIntertwining⟩
  · subst hnn
    exact ⟨serreWeight_eq_of_modEq (k := k) (n := n) h ▸ Representation.Equiv.refl _⟩

end TauCeti
