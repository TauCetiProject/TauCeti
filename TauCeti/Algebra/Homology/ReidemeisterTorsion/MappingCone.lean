/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ModuleCat.HomotopyCofiber
public import TauCeti.Algebra.Homology.ModuleCat.Shift.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# Torsion of shifted complexes and of mapping cones

The torsion of based chain complexes over a field is not invariant under quasi-isomorphisms, nor
even under chain homotopy equivalences, of based complexes: it changes by the torsion of the
mapping cone. This file proves this transformation law.

Let `C` be a based chain complex and let `D` be `C` shifted up by one degree with negated
differentials: isomorphisms `e i : D.X (i + 1) ≃ C.X i` turn the differential of `D` into the
negative of that of `C`, and carry the basis of `D.X (i + 1)` to that of `C.X i`. Then `D` is
acyclic exactly when `C` is (`HomologicalComplex.acyclic_iff_of_shift`, from
`TauCeti.Algebra.Homology.ModuleCat.Shift.Basic`), and `τ(D) = ε · τ(C)⁻¹` with
`ε = ∏ⱼ (-1) ^ (dim Bⱼ)`, where `Bⱼ ⊆ Cⱼ` is the space of boundaries
(`HomologicalComplex.reidemeisterTorsion_eq_mul_inv_of_shift`). Indeed the brackets of `D` are
those of `C` in the previous degree, up to the sign coming from the negated lifts, and they enter
the torsion with the opposite exponents.

The mapping cone `homotopyCofiber φ` of a chain map `φ : K ⟶ L` has the term
`K.X (i - 1) ⊞ L.X i` in degree `i`. Bases of `K` and `L` give it the basis
`HomologicalComplex.homotopyCofiber.basis`, from
`TauCeti.Algebra.Homology.ModuleCat.HomotopyCofiber`: the basis of `L.X i` followed by that of
`K.X (i - 1)`. The cone sits in the degreewise split short exact sequence
`L ⟶ cone φ ⟶ cone (K ⟶ 0)`, whose last term is `K` shifted up by one degree with negated
differentials, and whose bases are compatible. The multiplicativity of the torsion and the shift
formula give, for `K` acyclic, `τ(cone φ) = ε · τ(L) · τ(K)⁻¹` with the sign
`ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))`
(`HomologicalComplex.reidemeisterTorsion_homotopyCofiber`). For a quasi-isomorphism `φ` with `K`
bounded, this reads `τ(L) = ε · τ(cone φ) · τ(K)`
(`HomologicalComplex.reidemeisterTorsion_eq_mul_of_quasiIso`); the cone of a quasi-isomorphism is
acyclic, so this compares the torsions of `K` and `L` through the torsion of the cone, which is
in general not `±1`.

A complex `C` that is not acyclic has torsion `0`, but a choice of bases `h i` of its homology
groups gives the torsion `τ(C, c, h)` (`HomologicalComplex.reidemeisterTorsionWithHomology`),
nonzero for a bounded complex. This is the torsion of an acyclic mapping cone. Let `G` be a
complex with zero differential and bases `g i` of `G.X i`, and let `ζ : G ⟶ C` be a chain map
carrying each `g i k` to a cycle representing `h i k`; for instance `G` may be the complex of
homology groups of `C`, with `g = h`. Every cycle of `C` is then a boundary plus a value of `ζ`,
and a value of `ζ` is a boundary only if it is zero, so the mapping cone of `ζ` is acyclic. This
holds over any ring and needs no bases: the mapping cone of a chain map from a complex with zero
differential is acyclic as soon as the chain map induces bijections from the terms of that complex
onto the homology groups of its target (`HomologicalComplex.acyclic_homotopyCofiber_of_bijective`,
from `TauCeti.Algebra.Homology.ModuleCat.HomotopyCofiber`); here the bijections hold because `ζ`
carries the bases `g i` to cycles representing the bases `h i`
(`HomologicalComplex.moduleCatHomologyClass_bijective_of_basis`). The boundaries of the cone of
`ζ` in degree `j` are the cycles `Zⱼ` of `C`, based by a basis of the boundaries `Bⱼ` followed by
the representatives `ζ (g j)`, and these lift to the lifts of the basis of `Bⱼ` followed by the
basis `g j`. So the brackets of the cone are exactly the brackets `[bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁]` of `C`
with its homology bases, and `τ(cone ζ) = τ(C, c, h)`, with no sign
(`HomologicalComplex.reidemeisterTorsion_homotopyCofiber_eq_reidemeisterTorsionWithHomology`).
The torsion of a complex with based homology is thereby the torsion of a based acyclic complex,
to which the formulas for acyclic complexes apply.

## Main declarations

* `HomologicalComplex.reidemeisterTorsion_eq_mul_inv_of_shift`: the torsion of a shifted complex
  is, up to sign, the inverse of the torsion of the original complex.
* `HomologicalComplex.reidemeisterTorsion_homotopyCofiber`: the torsion of a mapping cone.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_quasiIso`: the change of the torsion under a
  quasi-isomorphism of based complexes.
* `HomologicalComplex.reidemeisterTorsion_homotopyCofiber_eq_reidemeisterTorsionWithHomology`: the
  torsion of the acyclic mapping cone of a chain map carrying bases to cycles representing homology
  bases is the torsion of the complex with these homology bases.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1 and §3.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F]

section Shift

variable {C D : ChainComplex (ModuleCat F) ℤ} (e : ∀ i, D.X (i + 1) ≃ₗ[F] C.X i)
  (he : ∀ i x, e i ((D.d (i + 1 + 1) (i + 1)).hom x) = -(C.d (i + 1) i).hom (e (i + 1) x))

variable {n m : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))
  (d : ∀ i, Basis (Fin (m i)) F (D.X i)) (hm : ∀ i, m (i + 1) = n i)
  (hd : ∀ i k, e i (d (i + 1) k) = c i (Fin.cast (hm i) k))

include he hd in
/-- The bracket of `C` in degree `j + 1`, computed with the images under `e` of boundary bases of
`D` and with the negated images of lifts in `D`, is `(-1) ^ q` times the bracket of `D` in degree
`j + 2`, where `q` is the dimension of the boundaries of `D` in degree `j + 1`. -/
private theorem torsionBracket_of_shift {j : ℤ} (h : D.ExactAt (j + 1 + 1))
    (h' : C.ExactAt (j + 1)) {p q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (D.d (j + 1 + 1 + 1) (j + 1 + 1)).hom))
    (b₀ : Basis (Fin q) F (LinearMap.range (D.d (j + 1 + 1) (j + 1)).hom))
    (s : Fin q → D.X (j + 1 + 1)) (hs : ∀ k, (D.d (j + 1 + 1) (j + 1)).hom (s k) = b₀ k)
    (hs' : ∀ k, (C.d (j + 1) j).hom (-e (j + 1) (s k)) =
      b₀.map (boundaryEquivOfShift e he j) k) :
    torsionBracket c (by simp) (by simp) h' (b₁.map (boundaryEquivOfShift e he (j + 1)))
        (b₀.map (boundaryEquivOfShift e he j)) (fun k ↦ -e (j + 1) (s k)) hs' =
      (-1) ^ q * torsionBracket d (by simp) (by simp) h b₁ b₀ s hs :=
  torsionBracket_eq_pow_mul d _ _ h b₁ b₀ s hs _ _ h' _ _ _ hs' (e (j + 1)) (hm (j + 1)).symm
    (fun k ↦ by simp [hd]) (fun k ↦ by simp) (-1) fun k ↦ by simp

include he hd in
/-- **The torsion of a shifted complex.** Let `D` be the complex `C` shifted up by one degree with
negated differentials: there are isomorphisms `e i : D.X (i + 1) ≃ C.X i` under which the
differential of `D` becomes the negative of that of `C`, and `e i` sends the basis `d (i + 1)` of
`D.X (i + 1)` to the basis `c i` of `C.X i`. Then `τ(D) = ε · τ(C)⁻¹`, where
`ε = ∏ⱼ (-1) ^ (dim Bⱼ)` and `Bⱼ ⊆ Cⱼ` is the space of boundaries of `C` in degree `j`. This holds
for every complex, both sides being `0` when `C` is not acyclic or is unbounded. -/
theorem reidemeisterTorsion_eq_mul_inv_of_shift :
    D.reidemeisterTorsion d =
      (∏ᶠ j : ℤ, (-1 : F) ^ finrank F (LinearMap.range (C.d (j + 1) j).hom)) *
        (C.reidemeisterTorsion c)⁻¹ := by
  -- A shifted complex is bounded exactly when the original one is.
  have hfin : {i | m i ≠ 0}.Finite ↔ {i | n i ≠ 0}.Finite := by
    have himage : {i | m i ≠ 0} = (· + 1) '' {i | n i ≠ 0} := by
      ext i
      refine ⟨fun hi ↦ ⟨i - 1, ?_, by simp⟩, ?_⟩
      · have := hm (i - 1)
        rw [sub_add_cancel] at this
        simpa [← this] using hi
      · rintro ⟨j, hj, rfl⟩
        simpa [hm] using hj
    rw [himage, Set.finite_image_iff (add_left_injective (1 : ℤ)).injOn]
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [reidemeisterTorsion_of_not_finite _ _ hn,
      reidemeisterTorsion_of_not_finite _ _ (mt hfin.1 hn)]
  by_cases hC : C.Acyclic
  swap
  · simp [reidemeisterTorsion_of_not_acyclic _ _ hC,
      reidemeisterTorsion_of_not_acyclic _ _ (mt (acyclic_iff_of_shift e he).1 hC)]
  have hD := (acyclic_iff_of_shift e he).2 hC
  have : ∀ i, Module.Finite F (D.X i) := fun i ↦ .of_basis (d i)
  -- Compute the torsion of `D` with arbitrary boundary bases `b'` and lifts `s'`, and that of `C`
  -- with their images `b` under `e` and the negated images `s` of the lifts.
  let b' (j : ℤ) := finBasis F (LinearMap.range (D.d (j + 1) j).hom)
  let s' (j : ℤ) (k : Fin (finrank F (LinearMap.range (D.d (j + 1) j).hom))) : D.X (j + 1) :=
    Function.surjInv (D.d (j + 1) j).hom.surjective_rangeRestrict (b' j k)
  have hs' (j : ℤ) (k) : (D.d (j + 1) j).hom (s' j k) = b' j k :=
    congrArg Subtype.val (Function.surjInv_eq (D.d (j + 1) j).hom.surjective_rangeRestrict _)
  let b (j : ℤ) := (b' (j + 1)).map (boundaryEquivOfShift e he j)
  have hs (j : ℤ) (k) : (C.d (j + 1) j).hom (-e (j + 1) (s' (j + 1) k)) = b j k := by
    simp [b, ← he, hs']
  have hq (j : ℤ) : finrank F (LinearMap.range (D.d (j + 1 + 1) (j + 1)).hom) =
      finrank F (LinearMap.range (C.d (j + 1) j).hom) :=
    (boundaryEquivOfShift e he j).finrank_eq
  have hε : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    simpa using hasFiniteMulSupport_neg_one_pow_finrank_mul C c hn fun _ ↦ 1
  have hτ : Function.HasFiniteMulSupport fun j : ℤ ↦
      (torsionBracket c (by simp) (by simp) (hC (j + 1)) (b (j + 1)) (b j) _ (hs j) ^
        (j.negOnePow : ℤ))⁻¹ :=
    (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        rw [torsionBracket_eq_one c _ _ _ _ _ _ _ (by simpa using hj), one_zpow, inv_one]
  rw [reidemeisterTorsion_eq_finprod (hfin.2 hn) hD b' s' hs',
    reidemeisterTorsion_eq_finprod hn hC b _ hs, ← finprod_inv_distrib,
    ← finprod_mul_distrib hε hτ, ← finprod_comp_equiv (Equiv.addRight (1 : ℤ))]
  refine finprod_congr fun j ↦ ?_
  -- The bracket of `D` in degree `j + 2` is `±` the bracket of `C` in degree `j + 1`, and enters
  -- the torsion with the opposite exponent.
  have hβ := torsionBracket_of_shift e he c d hm hd (hD (j + 1 + 1)) (hC (j + 1)) (b' (j + 1 + 1))
    (b' (j + 1)) (s' (j + 1)) (hs' (j + 1)) (hs j)
  rw [Equiv.coe_addRight, hβ, ← hq j]
  rcases Int.units_eq_one_or j.negOnePow with hj | hj
  · simp [Int.negOnePow_succ, hj]
    field_simp
  · simp [Int.negOnePow_succ, hj, ← mul_assoc, ← mul_pow]

end Shift

section MappingCone

open Limits ZeroObject

open homotopyCofiber in
/-- **The torsion of a mapping cone.** Let `φ : K ⟶ L` be a chain map of based complexes with `K`
acyclic, and give its mapping cone `homotopyCofiber φ`, whose term in degree `i` is
`K.X (i - 1) ⊞ L.X i`, the basis `homotopyCofiber.basis` made of the basis of `L.X i` followed by
that of `K.X (i - 1)`. Then `τ(cone φ) = ε · τ(L) · τ(K)⁻¹`, with the sign
`ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))` given by the dimensions of the boundaries
`B(K)ⱼ ⊆ Kⱼ` and `B(L)ⱼ ⊆ Lⱼ`. When `L` is not acyclic, neither is the cone, and both sides
are `0`. -/
theorem reidemeisterTorsion_homotopyCofiber {K L : ChainComplex (ModuleCat F) ℤ} (φ : K ⟶ L)
    {nK nL : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) F (K.X i))
    (cL : ∀ i, Basis (Fin (nL i)) F (L.X i)) (hK : K.Acyclic) :
    (homotopyCofiber φ).reidemeisterTorsion (basis φ cK cL) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      (L.reidemeisterTorsion cL * (K.reidemeisterTorsion cK)⁻¹) := by
  have hc : ∀ j, ∃ i, (ComplexShape.down ℤ).Rel i j := fun j ↦ ⟨j + 1, by simp⟩
  -- The mapping cone of `K ⟶ 0` is `K` shifted up by one degree, with negated differentials.
  let e (i : ℤ) : (homotopyCofiber (0 : K ⟶ 0)).X (i + 1) ≃ₗ[F] K.X i :=
    zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel (i + 1) i)
  have he (i : ℤ) := zeroEquiv_d K (i := i + 1 + 1) (j := i + 1) (k := i) (by simp) (by simp)
  have hm (i : ℤ) : nK (i + 1 - 1) = nK i := by simp
  have hshift := reidemeisterTorsion_eq_mul_inv_of_shift e he cK (zeroBasis cK) hm
    (zeroEquiv_zeroBasis cK)
  have hq (j : ℤ) : finrank F (LinearMap.range
      ((homotopyCofiber (0 : K ⟶ 0)).d (j + 1 + 1) (j + 1)).hom) =
      finrank F (LinearMap.range (K.d (j + 1) j).hom) :=
    (boundaryEquivOfShift e he j).finrank_eq
  have hS := coneShortComplex_shortExact φ hc
  have h₃ := (acyclic_iff_of_shift e he).2 hK
  by_cases hL : L.Acyclic
  swap
  · -- If the cone were acyclic, its projection to the acyclic cone of `K ⟶ 0` would be a
    -- quasi-isomorphism, and its kernel `L` would be acyclic.
    have hcone : ¬(homotopyCofiber φ).Acyclic := fun h ↦
      hL (hS.acyclic_X₁ ((quasiIso_iff _).2 fun i ↦ (quasiIsoAt_iff_exactAt _ i (h i)).2 (h₃ i)))
    simp [reidemeisterTorsion_of_not_acyclic _ _ hL, reidemeisterTorsion_of_not_acyclic _ _ hcone]
  -- The multiplicativity of the torsion in `L ⟶ cone φ ⟶ cone (K ⟶ 0)`.
  have hmul := reidemeisterTorsion_eq_mul_of_shortExact hS hL h₃ cL (zeroBasis cK) (basis φ cK cL)
    (fun i k ↦ basis_castAdd φ cK cL i k) (fun i k ↦ by
      rw [basis_natAdd, zeroBasis_apply]
      have h₀ := inlX_mapArrowHom_f φ (0 : K ⟶ 0) hc (Arrow.homMk (𝟙 K) 0) (i - 1) i (by simp)
      have h := congr(($h₀).hom (cK (i - 1) k))
      simp only [Arrow.homMk_left, id_f] at h
      exact h)
  rw [hmul, hshift]
  simp only [hq]
  by_cases hn : {i | nK i ≠ 0}.Finite
  swap
  · simp [reidemeisterTorsion_of_not_finite _ _ hn]
  -- Combine the Koszul sign of the multiplicativity formula with the sign of the shift.
  have hε := finprod_mul_distrib
    (hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hn fun j ↦
      finrank F (LinearMap.range (L.d (j + 1) j).hom))
    (hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hn fun _ ↦ 1)
  simp only [mul_one, ← pow_add, ← mul_add_one] at hε
  rw [hε]
  ring

open homotopyCofiber in
/-- **The torsion under a quasi-isomorphism.** The torsion of based complexes is not invariant
under quasi-isomorphisms, nor even under chain homotopy equivalences; it changes by the torsion of
the mapping cone. If `φ : K ⟶ L` is a quasi-isomorphism of based complexes with `K` bounded, then
`τ(L) = ε · τ(cone φ) · τ(K)`, where the mapping cone has the basis `homotopyCofiber.basis` and
`ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))` is the sign of
`HomologicalComplex.reidemeisterTorsion_homotopyCofiber`. When `K` is not acyclic, neither is `L`,
and both sides are `0`. -/
theorem reidemeisterTorsion_eq_mul_of_quasiIso {K L : ChainComplex (ModuleCat F) ℤ} (φ : K ⟶ L)
    [QuasiIso φ] {nK nL : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) F (K.X i))
    (cL : ∀ i, Basis (Fin (nL i)) F (L.X i)) (hn : {i | nK i ≠ 0}.Finite) :
    L.reidemeisterTorsion cL =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      ((homotopyCofiber φ).reidemeisterTorsion (basis φ cK cL) * K.reidemeisterTorsion cK) := by
  have hKL : K.Acyclic ↔ L.Acyclic := forall_congr' fun i ↦ exactAt_iff_of_quasiIsoAt φ i
  by_cases hK : K.Acyclic
  swap
  · simp [reidemeisterTorsion_of_not_acyclic _ _ hK,
      reidemeisterTorsion_of_not_acyclic _ _ (mt hKL.2 hK)]
  -- The sign squares to `1`, and `τ(K)` is nonzero.
  have hsupp := hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hn fun j ↦
    finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1
  have hε : (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
      (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) = 1 := by
    rw [← finprod_mul_distrib hsupp hsupp]
    simp [← mul_pow]
  rw [reidemeisterTorsion_homotopyCofiber φ cK cL hK]
  simp [← mul_assoc, hε, reidemeisterTorsion_ne_zero K cK hn hK]

end MappingCone

section HomologySection

open homotopyCofiber

variable {C G : ChainComplex (ModuleCat F) ℤ} (ζ : G ⟶ C) (hG : ∀ i j, G.d i j = 0)
  {m : ℤ → ℕ} (g : ∀ i, Basis (Fin (m i)) F (G.X i))
  (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
  (y : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
  (hζ : ∀ i k, C.iCycles i (y i k) = ζ.f i (g i k))

/-- The basis of the boundaries of the mapping cone in degree `j`: a basis of the boundaries `Bⱼ`
of `C` followed by the cycles representing the homology basis `h j`, included into the cone. -/
private def coneBoundaryBasis {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (j : ℤ) :
    Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom) + m j)) F
      (LinearMap.range ((homotopyCofiber ζ).d (j + 1) j).hom) :=
  ((kerBasisOfHomology (ChainComplex.prev ℤ j) (ChainComplex.next ℤ j)
    (chosenBoundaryBasis C c (j + 1) j) (h j) (y j) (hy j)).map
      ((LinearEquiv.ofInjective ((inrX ζ j).hom ∘ₗ (LinearMap.ker (C.d j (j - 1)).hom).subtype)
        ((inrX_hom_injective ζ j).comp Subtype.val_injective)).trans
        (LinearEquiv.ofEq _ _ (range_inrX_comp_subtype ζ hG
          fun i ↦ moduleCatHomologyClass_bijective_of_basis C _ _ _ (g i) (h i) (y i) (hy i)
            (hζ i))))).reindex
    finSumFinEquiv

private theorem coe_coneBoundaryBasis {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (j : ℤ)
    (k : Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom) + m j)) :
    (coneBoundaryBasis ζ hG g h y hy hζ c j k : (homotopyCofiber ζ).X j) =
      (inrX ζ j).hom (Fin.append (fun k ↦ (chosenBoundaryBasis C c (j + 1) j k : C.X j))
        (fun k ↦ C.iCycles j (y j k)) k) := by
  induction k using Fin.addCases <;> simp [coneBoundaryBasis]

/-- Lifts to the mapping cone of the basis `coneBoundaryBasis` of its boundaries. -/
private def coneLift {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (j : ℤ) :
    Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom) + m j) → (homotopyCofiber ζ).X (j + 1) :=
  Fin.append (fun k ↦ (inrX ζ (j + 1)).hom (chosenBoundaryLift C c (j + 1) j k))
    fun k ↦ (inlX ζ j (j + 1) (by simp)).hom (g j k)

private theorem coneLift_spec {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (j : ℤ) (k) :
    ((homotopyCofiber ζ).d (j + 1) j).hom (coneLift ζ g c j k) =
      coneBoundaryBasis ζ hG g h y hy hζ c j k := by
  rw [coe_coneBoundaryBasis, homotopyCofiber_d]
  induction k using Fin.addCases with
  | left k => simp [coneLift, chosenBoundaryLift_spec]
  | right k => simp [coneLift, inlX_d_apply_of_d_eq_zero ζ _ (hG _ _), hζ]

/-- Including the basis of `G.X a` into the mapping cone along `a = j`; the degrees `j` and
`j + 1 - 1` are only propositionally equal. -/
private theorem inlX_hom_cast {j a : ℤ} (ha : a = j) (k : Fin (m a))
    (h₁ : (ComplexShape.down ℤ).Rel (j + 1) a) (h₂ : (ComplexShape.down ℤ).Rel (j + 1) j) :
    (inlX ζ j (j + 1) h₂).hom (g j (Fin.cast (by rw [ha]) k)) =
      (inlX ζ a (j + 1) h₁).hom (g a k) := by
  subst ha
  rfl

include hG hy hζ in
/-- The brackets of the mapping cone are the brackets of `C` with its homology bases. -/
private theorem torsionBracket_coneBoundaryBasis {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (j : ℤ) (hj : (homotopyCofiber ζ).ExactAt (j + 1)) :
    torsionBracket (basis ζ g c) (by simp) (by simp) hj
        (coneBoundaryBasis ζ hG g h y hy hζ c (j + 1)) (coneBoundaryBasis ζ hG g h y hy hζ c j)
        (coneLift ζ g c j) (coneLift_spec ζ hG g h y hy hζ c j) =
      torsionBracketWithHomology c (by simp) (by simp)
        (chosenBoundaryBasis C c (j + 1 + 1) (j + 1)) (h (j + 1))
        (y (j + 1)) (hy (j + 1)) (chosenBoundaryBasis C c (j + 1) j)
        (chosenBoundaryLift C c (j + 1) j) (chosenBoundaryLift_spec C c (j + 1) j) := by
  have hn₁ := eq_add_of_exactAt (basis ζ g c) (by simp) (by simp) hj
    (coneBoundaryBasis ζ hG g h y hy hζ c (j + 1)) (coneBoundaryBasis ζ hG g h y hy hζ c j)
  have hm : m (j + 1 - 1) = m j := by rw [add_sub_cancel_right]
  have hn₂ : n (j + 1) = finrank F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom) + m (j + 1) +
      finrank F (LinearMap.range (C.d (j + 1) j).hom) := by omega
  set u := Fin.append (Fin.append (fun k ↦ (chosenBoundaryBasis C c (j + 1 + 1) (j + 1) k :
    C.X (j + 1))) fun k ↦ C.iCycles (j + 1) (y (j + 1) k)) (chosenBoundaryLift C c (j + 1) j) ∘
      Fin.cast hn₂ with hu
  rw [torsionBracket_eq_det_append (basis ζ g c) _ _ hj _ _ _ _ hn₁,
    torsionBracketWithHomology_eq_det_append c _ _ _ _ _ _ _ _ _ hn₂, ← hu,
    basis_det_eq_mul ζ g c (j + 1) _ u (g (j + 1 - 1)), Basis.det_self, mul_one]
  · intro k
    obtain ⟨k, rfl⟩ := (finCongr hn₂).symm.surjective k
    -- The index `k` of `u` sits in the cone family at the index with the same value.
    have hk (k' : Fin _) (hk' : (k : ℕ) = k') :
        Fin.cast hn₁ (Fin.castAdd (m (j + 1 - 1)) (Fin.cast hn₂.symm k)) = k' :=
      Fin.ext hk'
    simp only [hu, Function.comp_apply, finCongr_symm, finCongr_apply]
    induction k using Fin.addCases with
    | left k =>
      rw [hk (Fin.castAdd _ k) (by simp), Fin.append_left, coe_coneBoundaryBasis]
      simp
    | right k =>
      rw [hk (Fin.natAdd _ (Fin.castAdd _ k)) (by simp)]
      simp [coneLift]
  · intro k
    have hk : Fin.cast hn₁ (Fin.natAdd (n (j + 1)) k) =
        Fin.natAdd _ (Fin.natAdd _ (Fin.cast hm k)) :=
      Fin.ext (by simp; omega)
    simp only [Function.comp_apply, hk, Fin.append_right, coneLift]
    exact inlX_hom_cast ζ g (add_sub_cancel_right j 1) k _ _

include hG hy hζ in
/-- **The torsion with homology bases is the torsion of a mapping cone.** Let `ζ : G ⟶ C` be a
chain map from a complex `G` with zero differential, with bases `g i` of `G.X i`, which carries
each basis vector `g i k` to a cycle representing the vector `h i k` of a basis of `Hᵢ(C)`. Then
the mapping cone of `ζ` is acyclic (`acyclic_homotopyCofiber_of_bijective`, applied to
`moduleCatHomologyClass_bijective_of_basis`), and its torsion, for
the basis `homotopyCofiber.basis` made of the basis of `C.X i` followed by that of `G.X (i - 1)`,
is the torsion `τ(C, c, h)` of `C` with the homology bases `h`. -/
theorem reidemeisterTorsion_homotopyCofiber_eq_reidemeisterTorsionWithHomology {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    (homotopyCofiber ζ).reidemeisterTorsion (basis ζ g c) =
      C.reidemeisterTorsionWithHomology c h := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · rw [reidemeisterTorsionWithHomology_of_not_finite _ _ _ hn,
      reidemeisterTorsion_of_not_finite _ _ fun h' ↦ hn (h'.subset fun i hi ↦ by
        simp only [Set.mem_ofPred_eq] at hi ⊢
        omega)]
  have hn' : {i | n i + m (i - 1) ≠ 0}.Finite := by
    refine (hn.union (hn.image (· + 1))).subset fun i hi ↦ ?_
    by_cases h0 : n i = 0
    · refine Or.inr ⟨i - 1, fun h1 ↦ hi ?_, by simp⟩
      have := Module.Finite.of_basis (c (i - 1))
      have := C.finrank_homology_le_finrank_X (i - 1)
      rw [finrank_eq_card_basis (h (i - 1)), finrank_eq_card_basis (c (i - 1))] at this
      simp only [Fintype.card_fin] at this
      omega
    · exact Or.inl h0
  have hacyc := acyclic_homotopyCofiber_of_bijective ζ hG
    fun i ↦ moduleCatHomologyClass_bijective_of_basis C _ _ _ (g i) (h i) (y i) (hy i) (hζ i)
  rw [reidemeisterTorsionWithHomology_eq_finprod hn (fun j ↦ chosenBoundaryBasis C c (j + 1) j) y
      hy (fun j ↦ chosenBoundaryLift C c (j + 1) j) (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    reidemeisterTorsion_eq_finprod hn' hacyc (coneBoundaryBasis ζ hG g h y hy hζ c)
      (coneLift ζ g c) (coneLift_spec ζ hG g h y hy hζ c)]
  exact finprod_congr fun j ↦ by
    rw [torsionBracket_coneBoundaryBasis ζ hG g h y hy hζ c j (hacyc (j + 1))]

end HomologySection

end HomologicalComplex
