/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence
public import TauCeti.Algebra.Homology.ModuleCat.HomotopyCofiber
public import TauCeti.Algebra.Homology.ModuleCat.Shift.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Append

/-!
# Torsion of shifted complexes and of mapping cones

The torsion of based chain complexes over a field is not invariant under quasi-isomorphisms, nor
even under chain homotopy equivalences, of based complexes: it changes by the torsion of the
mapping cone. This file proves this transformation law, both for acyclic complexes and for general
complexes with based homology.

Let `C` be a based chain complex and let `D` be `C` shifted up by one degree with negated
differentials: isomorphisms `e i : D.X (i + 1) ≃ C.X i` turn the differential of `D` into the
negative of that of `C`, and carry the basis of `D.X (i + 1)` to that of `C.X i`. Then `D` is
acyclic exactly when `C` is (`HomologicalComplex.acyclic_iff_of_shift`, from
`TauCeti.Algebra.Homology.ModuleCat.Shift.Basic`), and `τ(D) = ε · τ(C)⁻¹` with
`ε = ∏ⱼ (-1) ^ (dim Bⱼ)`, where `Bⱼ ⊆ Cⱼ` is the space of boundaries
(`HomologicalComplex.reidemeisterTorsion_eq_mul_inv_of_shift`). More generally, if homology bases
`hD (i + 1)` and `hC i` correspond under `HomologicalComplex.homologyEquivOfShift`, then
`τ(D, d, hD) = ε · τ(C, c, hC)⁻¹`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_inv_of_shift`). Indeed the brackets of
`D` are those of `C` in the previous degree, up to the sign coming from the negated lifts, and they
enter the torsion with the opposite exponents.

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
(`HomologicalComplex.reidemeisterTorsion_eq_mul_of_quasiIso`).

Without assuming acyclicity, if `φ : K ⟶ L` is a quasi-isomorphism then `cone φ` is acyclic and the
connecting maps of `L ⟶ cone φ ⟶ cone (K ⟶ 0)` identify with `Hᵢ(φ)`, so the homology sequence has
torsion `1` when `L` inherits its homology bases from `K` along `φ`. Multiplicativity through the
homology sequence then gives `τ(cone φ) = ε · τ(L, cL, φ_* hK) · τ(K, cK, hK)⁻¹`
(`HomologicalComplex.reidemeisterTorsion_homotopyCofiber_of_quasiIso`), and for bounded `K` and any
homology bases `hK` of `K` and `hL` of `L`,
`τ(L, cL, hL) = ε · τ(cone φ) · τ(K, cK, hK) · ∏ᵢ det(Hᵢ(φ)) ^ ((-1) ^ i)`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_quasiIso`).

## Main declarations

* `HomologicalComplex.reidemeisterTorsion_eq_mul_inv_of_shift`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_inv_of_shift`: the torsion of a
  shifted complex is, up to sign, the inverse of the torsion of the original complex.
* `HomologicalComplex.reidemeisterTorsion_homotopyCofiber`,
  `HomologicalComplex.reidemeisterTorsion_homotopyCofiber_of_quasiIso`: the torsion of a mapping
  cone.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_quasiIso`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_map_eq_mul_of_quasiIso`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_quasiIso`: the change of the
  torsion under a quasi-isomorphism of based complexes.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1 and §3.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F]

private theorem finite_iff_of_shift {n m : ℤ → ℕ} (hm : ∀ i, m (i + 1) = n i) :
    {i | m i ≠ 0}.Finite ↔ {i | n i ≠ 0}.Finite := by
  have himage : {i | m i ≠ 0} = (· + 1) '' {i | n i ≠ 0} := by
    ext i
    refine ⟨fun hi ↦ ⟨i - 1, ?_, by simp⟩, ?_⟩
    · have := hm (i - 1)
      rw [sub_add_cancel] at this
      simpa [← this] using hi
    · rintro ⟨j, hj, rfl⟩
      simpa [hm] using hj
  rw [himage, Set.finite_image_iff (add_left_injective (1 : ℤ)).injOn]

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
      (-1) ^ q * torsionBracket d (by simp) (by simp) h b₁ b₀ s hs := by
  have : Module.Finite F (D.X (j + 1 + 1)) := .of_basis (d _)
  have hn : m (j + 1 + 1) = p + q := by
    have := (exactAt_iff_finrank_add_finrank D (i := j + 1 + 1 + 1) (k := j + 1) (by simp)
      (by simp)).1 h
    rwa [finrank_eq_card_basis b₁, finrank_eq_card_basis b₀, finrank_eq_card_basis (d _),
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, eq_comm] at this
  -- The basis of `C.X (j + 1)` is the transport along `e` of the basis of `D.X (j + 1 + 1)`.
  have hc : c (j + 1) = ((d (j + 1 + 1)).map (e (j + 1))).reindex (finCongr (hm (j + 1))) :=
    Basis.eq_of_apply_eq fun k ↦ by simp [hd]
  rw [torsionBracket_eq_det_append c _ _ h' _ _ _ hs' ((hm (j + 1)).symm.trans hn),
    torsionBracket_eq_det_append d _ _ h _ _ _ hs hn, hc, Basis.det_reindex, Basis.det_map]
  have hneg := ((d (j + 1 + 1)).det.domDomCongr (finCongr hn)).map_append_neg
    (fun k ↦ (b₁ k : D.X (j + 1 + 1))) s
  have hcast : (finCongr hn : Fin (m (j + 1 + 1)) → Fin (p + q)) = Fin.cast hn := rfl
  rw [AlternatingMap.domDomCongr_apply, AlternatingMap.domDomCongr_apply, hcast,
    smul_eq_mul] at hneg
  rw [← hneg]
  congr 1
  ext k
  obtain ⟨l, rfl⟩ := (finCongr hn.symm).surjective k
  induction l using Fin.addCases <;> simp

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
  have hfin := finite_iff_of_shift hm
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

variable {μ ν : ℤ → ℕ} (hC : ∀ i, Basis (Fin (μ i)) F (C.homology i))
  (hD : ∀ i, Basis (Fin (ν i)) F (D.homology i)) (hν : ∀ i, ν (i + 1) = μ i)
  (hhD : ∀ i k, homologyEquivOfShift e he i (hD (i + 1) k) = hC i (Fin.cast (hν i) k))

include he hd in
/-- The based-homology bracket of `C` in degree `j + 1`, computed with the images under `e` of
boundary bases and cycle representatives of `D` and with the negated images of lifts in `D`, is
`(-1) ^ q` times the bracket of `D` in degree `j + 2`. -/
private theorem torsionBracketWithHomology_of_shift {j : ℤ} {p q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (D.d (j + 1 + 1 + 1) (j + 1 + 1)).hom))
    (yD : Fin (ν (j + 1 + 1)) → D.cycles (j + 1 + 1))
    (hyD : ∀ k, D.homologyπ (j + 1 + 1) (yD k) = hD (j + 1 + 1) k)
    (b₀ : Basis (Fin q) F (LinearMap.range (D.d (j + 1 + 1) (j + 1)).hom))
    (s : Fin q → D.X (j + 1 + 1)) (hs : ∀ k, (D.d (j + 1 + 1) (j + 1)).hom (s k) = b₀ k)
    (hyC : ∀ k, C.homologyπ (j + 1)
      (cyclesEquivOfShift e he (j + 1) (yD (Fin.cast (hν (j + 1)).symm k))) = hC (j + 1) k)
    (hs' : ∀ k, (C.d (j + 1) j).hom (-e (j + 1) (s k)) =
      b₀.map (boundaryEquivOfShift e he j) k) :
    torsionBracketWithHomology c (b₁.map (boundaryEquivOfShift e he (j + 1))) (hC (j + 1))
        (fun k ↦ cyclesEquivOfShift e he (j + 1) (yD (Fin.cast (hν (j + 1)).symm k))) hyC
        (b₀.map (boundaryEquivOfShift e he j)) (fun k ↦ -e (j + 1) (s k)) hs' =
      (-1) ^ q * torsionBracketWithHomology d b₁ (hD (j + 1 + 1)) yD hyD b₀ s hs := by
  have hn := eq_add_add d b₁ (hD (j + 1 + 1)) yD hyD b₀ s hs
  have hnC : n (j + 1) = p + μ (j + 1) + q := by
    have := hm (j + 1); have := hν (j + 1); omega
  have hc : c (j + 1) = ((d (j + 1 + 1)).map (e (j + 1))).reindex (finCongr (hm (j + 1))) :=
    Basis.eq_of_apply_eq fun k ↦ by simp [hd]
  rw [torsionBracketWithHomology_eq_det_append c _ _ _ hyC _ _ hs' hnC,
    torsionBracketWithHomology_eq_det_append d _ _ _ hyD _ _ hs hn,
    hc, Basis.det_reindex, Basis.det_map]
  have hneg := ((d (j + 1 + 1)).det.domDomCongr (finCongr hn)).map_append_neg
    (Fin.append (fun k ↦ (b₁ k : D.X (j + 1 + 1)))
      (fun k ↦ (D.iCycles (j + 1 + 1)).hom (yD k))) s
  have hcast :
      (finCongr hn : Fin (m (j + 1 + 1)) → Fin (p + ν (j + 1 + 1) + q)) = Fin.cast hn := rfl
  rw [AlternatingMap.domDomCongr_apply, AlternatingMap.domDomCongr_apply, hcast,
    smul_eq_mul] at hneg
  rw [← hneg]
  congr 1
  ext k
  obtain ⟨l, rfl⟩ := (finCongr hn.symm).surjective k
  induction l using Fin.addCases with
  | left l =>
    have hr : Fin.cast hn ((finCongr hn.symm) (Fin.castAdd q l)) = Fin.castAdd q l :=
      Fin.ext (by simp)
    simp only [Function.comp_apply, hr, Fin.append_left]
    induction l using Fin.addCases with
    | left l =>
      simp only [finCongr_apply, Fin.cast_cast]
      rw [show Fin.cast _ (Fin.castAdd q (Fin.castAdd (ν (j + 1 + 1)) l)) =
        Fin.castAdd q (Fin.castAdd (μ (j + 1)) l) from Fin.ext (by simp)]
      simp
    | right l =>
      simp only [finCongr_apply, Fin.cast_cast]
      rw [show Fin.cast _ (Fin.castAdd q (Fin.natAdd p l)) =
        Fin.castAdd q (Fin.natAdd p (Fin.cast (hν (j + 1)) l)) from Fin.ext (by simp)]
      simp
  | right l => simp

include he hd hhD in
/-- **The torsion with based homology of a shifted complex.** Let `D` be `C` shifted up by one
degree with negated differentials: `e i : D.X (i + 1) ≃ C.X i` sends the differential of `D` to the
negative of that of `C` and `d (i + 1)` to `c i`, and `homologyEquivOfShift e he i` sends
`hD (i + 1)` to `hC i`. Then `τ(D, d, hD) = (∏ⱼ (-1) ^ (dim Bⱼ)) · τ(C, c, hC)⁻¹`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_inv_of_shift :
    D.reidemeisterTorsionWithHomology d hD =
      (∏ᶠ j : ℤ, (-1 : F) ^ finrank F (LinearMap.range (C.d (j + 1) j).hom)) *
        (C.reidemeisterTorsionWithHomology c hC)⁻¹ := by
  have hfin := finite_iff_of_shift hm
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [hn, mt hfin.1 hn]
  have : ∀ i, Module.Finite F (D.X i) := fun i ↦ .of_basis (d i)
  let b' (j : ℤ) := finBasis F (LinearMap.range (D.d (j + 1) j).hom)
  let s' (j : ℤ) (k : Fin (finrank F (LinearMap.range (D.d (j + 1) j).hom))) : D.X (j + 1) :=
    Function.surjInv (D.d (j + 1) j).hom.surjective_rangeRestrict (b' j k)
  have hs' (j : ℤ) (k) : (D.d (j + 1) j).hom (s' j k) = b' j k :=
    congrArg Subtype.val (Function.surjInv_eq (D.d (j + 1) j).hom.surjective_rangeRestrict _)
  let yD (i : ℤ) (k : Fin (ν i)) : D.cycles i :=
    Function.surjInv (D.moduleCat_homologyπ_surjective i) (hD i k)
  have hyD (i : ℤ) (k : Fin (ν i)) : D.homologyπ i (yD i k) = hD i k :=
    Function.surjInv_eq (D.moduleCat_homologyπ_surjective i) _
  let b (j : ℤ) := (b' (j + 1)).map (boundaryEquivOfShift e he j)
  let yC (i : ℤ) (k : Fin (μ i)) : C.cycles i :=
    cyclesEquivOfShift e he i (yD (i + 1) (Fin.cast (hν i).symm k))
  have hyC (i : ℤ) (k : Fin (μ i)) : C.homologyπ i (yC i k) = hC i k := by
    change (C.homologyπ i).hom (yC i k) = hC i k
    rw [← homologyEquivOfShift_homologyπ e he i]
    exact (congrArg (homologyEquivOfShift e he i) (hyD (i + 1) _)).trans
      ((hhD i _).trans (congrArg (hC i) (by simp)))
  have hs (j : ℤ) (k) : (C.d (j + 1) j).hom (-e (j + 1) (s' (j + 1) k)) = b j k := by
    simp [b, ← he, hs']
  have hq (j : ℤ) : finrank F (LinearMap.range (D.d (j + 1 + 1) (j + 1)).hom) =
      finrank F (LinearMap.range (C.d (j + 1) j).hom) :=
    (boundaryEquivOfShift e he j).finrank_eq
  have hε : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    simpa using hasFiniteMulSupport_neg_one_pow_finrank_mul C c hn fun _ ↦ 1
  have hτ : Function.HasFiniteMulSupport fun j : ℤ ↦
      (torsionBracketWithHomology c (b (j + 1)) (hC (j + 1)) (yC (j + 1)) (hyC (j + 1))
        (b j) _ (hs j) ^ (j.negOnePow : ℤ))⁻¹ :=
    (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        rw [torsionBracketWithHomology_eq_one c _ _ _ _ _ _ _ (by simpa using hj),
          one_zpow, inv_one]
  rw [reidemeisterTorsionWithHomology_eq_finprod (hfin.2 hn) b' yD hyD s' hs',
    reidemeisterTorsionWithHomology_eq_finprod hn b yC hyC _ hs, ← finprod_inv_distrib,
    ← finprod_mul_distrib hε hτ, ← finprod_comp_equiv (Equiv.addRight (1 : ℤ))]
  refine finprod_congr fun j ↦ ?_
  have hβ := torsionBracketWithHomology_of_shift e he c d hm hd hC hD hν (b' (j + 1 + 1))
    (yD (j + 1 + 1)) (hyD (j + 1 + 1)) (b' (j + 1)) (s' (j + 1)) (hs' (j + 1)) (hyC (j + 1)) (hs j)
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

open homotopyCofiber in
/-- **The torsion of the mapping cone of a quasi-isomorphism.** Let `φ : K ⟶ L` be a
quasi-isomorphism of based complexes, with homology bases `hK` of `K` transported to `L` along
`isoOfQuasiIsoAt φ`. Then the mapping cone `homotopyCofiber φ` is acyclic and

`τ(cone φ) = ε · τ(L, cL, φ_* hK) · τ(K, cK, hK)⁻¹`

with `ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))`. -/
theorem reidemeisterTorsion_homotopyCofiber_of_quasiIso
    {K L : ChainComplex (ModuleCat F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    {nK nL m : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) F (K.X i))
    (cL : ∀ i, Basis (Fin (nL i)) F (L.X i))
    (hK : ∀ i, Basis (Fin (m i)) F (K.homology i)) :
    (homotopyCofiber φ).reidemeisterTorsion (basis φ cK cL) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      (L.reidemeisterTorsionWithHomology cL
          (fun i ↦ (hK i).map (isoOfQuasiIsoAt φ i).toLinearEquiv) *
        (K.reidemeisterTorsionWithHomology cK hK)⁻¹) := by
  by_cases hn : {i | nL i + nK (i - 1) ≠ 0}.Finite
  swap
  · have hnot : ¬{i | nL i ≠ 0}.Finite ∨ ¬{i | nK i ≠ 0}.Finite := by
      by_contra! h
      have hK' : {i | nK (i - 1) ≠ 0}.Finite :=
        (h.2.image (· + 1)).subset fun i hi ↦ ⟨i - 1, hi, by simp⟩
      refine hn ((h.1.union hK').subset fun i hi ↦ ?_)
      by_contra h0
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h0 hi
      omega
    rw [reidemeisterTorsion_of_not_finite _ _ hn]
    rcases hnot with hnL | hnK
    · simp [hnL]
    · simp [hnK]
  have hnL : {i | nL i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by change nL i + nK (i - 1) ≠ 0; change nL i ≠ 0 at hi; omega
  have hnK_shift : {i | nK (i - 1) ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by change nL i + nK (i - 1) ≠ 0; change nK (i - 1) ≠ 0 at hi; omega
  have hnK : {i | nK i ≠ 0}.Finite :=
    (hnK_shift.image (· - 1)).subset fun i hi ↦ ⟨i + 1, by simpa using hi, by simp⟩
  have hc : ∀ j, ∃ i, (ComplexShape.down ℤ).Rel i j := fun j ↦ ⟨j + 1, by simp⟩
  let e (i : ℤ) : (homotopyCofiber (0 : K ⟶ 0)).X (i + 1) ≃ₗ[F] K.X i :=
    zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel (i + 1) i)
  have he (i : ℤ) := zeroEquiv_d K (i := i + 1 + 1) (j := i + 1) (k := i) (by simp) (by simp)
  have hm (i : ℤ) : nK (i + 1 - 1) = nK i := by simp
  have hν (i : ℤ) : m (i + 1 - 1) = m i := by simp
  have hS := coneShortComplex_shortExact φ hc
  have hcone_ac := acyclic_of_quasiIso φ hc
  let h₁ (i : ℤ) : Basis (Fin (m i)) F (L.homology i) :=
    (hK i).map (isoOfQuasiIsoAt φ i).toLinearEquiv
  have hsub₂ (i : ℤ) : Subsingleton ((homotopyCofiber φ).homology i) :=
    ModuleCat.subsingleton_of_isZero (hcone_ac i).isZero_homology
  let h₂ (i : ℤ) : Basis (Fin 0) F ((homotopyCofiber φ).homology i) := Basis.empty _
  let h₃_succ (q : ℤ) : Basis (Fin (m q)) F ((homotopyCofiber (0 : K ⟶ 0)).homology (q + 1)) :=
    (hK q).map (zeroHomologyEquiv K q).symm
  let h₃ (i : ℤ) : Basis (Fin (m (i - 1))) F ((homotopyCofiber (0 : K ⟶ 0)).homology i) :=
    (h₃_succ (i - 1)).map (eqToIso (congrArg
      (fun r ↦ (homotopyCofiber (0 : K ⟶ 0)).homology r) (sub_add_cancel i 1))).toLinearEquiv
  have hh₃_apply (q : ℤ) (k : Fin (m (q + 1 - 1))) :
      h₃ (q + 1) k = h₃_succ q (Fin.cast (hν q) k) := by
    have key : ∀ p (hp : p = q) (hp1 : p + 1 = q + 1) (k : Fin (m p)),
        ((h₃_succ p).map (eqToIso (congrArg
          (fun r ↦ (homotopyCofiber (0 : K ⟶ 0)).homology r) hp1)).toLinearEquiv) k =
          h₃_succ q (Fin.cast (congrArg m hp) k) := by
      rintro p rfl hp1 k
      have : hp1 = rfl := Subsingleton.elim _ _
      subst this
      simp
    exact key (q + 1 - 1) (by simp) (sub_add_cancel (q + 1) 1) k
  have hh₃ (q : ℤ) (k : Fin (m (q + 1 - 1))) :
      homologyEquivOfShift e he q (h₃ (q + 1) k) = hK q (Fin.cast (hν q) k) := by
    rw [← zeroHomologyEquiv_eq K q, hh₃_apply]
    simp [h₃_succ]
  have hshift := reidemeisterTorsionWithHomology_eq_mul_inv_of_shift e he cK (zeroBasis cK) hm
    (zeroEquiv_zeroBasis cK) hK h₃ hν hh₃
  have hq (j : ℤ) : finrank F (LinearMap.range
      ((homotopyCofiber (0 : K ⟶ 0)).d (j + 1 + 1) (j + 1)).hom) =
      finrank F (LinearMap.range (K.d (j + 1) j).hom) :=
    (boundaryEquivOfShift e he j).finrank_eq
  -- The homology sequence of `coneShortComplex φ` has torsion `1` for `(h₁, h₂, h₃)`.
  have hH₁ : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) = 1 := by
    have hδ_surj (q : ℤ) : Function.Surjective (hS.δ (q + 1) q rfl).hom := by
      rw [coneShortComplex_δ_eq φ hc q]
      exact (isoOfQuasiIsoAt φ q).toLinearEquiv.surjective.comp (zeroHomologyEquiv K q).surjective
    let α (q : ℤ) : Basis (Fin (m q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
      (h₁ q).map (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (hδ_surj q))).symm
    have : ∀ q, Subsingleton (LinearMap.range (homologyMap (coneShortComplex φ hc).f q).hom) :=
      fun _ ↦ inferInstance
    have : ∀ q, Subsingleton (LinearMap.range (homologyMap (coneShortComplex φ hc).g q).hom) :=
      fun q ↦ (homologyMap (coneShortComplex φ hc).g q).hom.surjective_rangeRestrict.subsingleton
    let β (q : ℤ) :
        Basis (Fin 0) F (LinearMap.range (homologyMap (coneShortComplex φ hc).f q).hom) :=
      Basis.empty _
    let γ (q : ℤ) :
        Basis (Fin 0) F (LinearMap.range (homologyMap (coneShortComplex φ hc).g q).hom) :=
      Basis.empty _
    let sα (q : ℤ) (k : Fin (m q)) : (homotopyCofiber (0 : K ⟶ 0)).homology (q + 1) :=
      h₃ (q + 1) (Fin.cast (hν q).symm k)
    have hsα (q : ℤ) (k : Fin (m q)) : (hS.δ (q + 1) q rfl).hom (sα q k) = α q k := by
      refine (LinearMap.congr_fun (coneShortComplex_δ_eq φ hc q) (sα q k)).trans ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, sα, hh₃_apply, h₃_succ,
        Fin.cast_cast, Fin.cast_refl, id_eq, Basis.map_apply, LinearEquiv.apply_symm_apply,
        α, LinearEquiv.ofTop_symm_apply, Subtype.coe_mk, h₁, Iso.toLinearEquiv_apply,
        isoOfQuasiIsoAt_hom]
    have hm₁ (q : ℤ) : m q = m q + 0 := (Nat.add_zero _).symm
    have hm₃ (q : ℤ) : m (q + 1 - 1) = 0 + m q := by simp
    refine reidemeisterTorsion_interleave_eq_one _ _ _ hS.acyclic_homologySequenceComplex
      h₁ h₂ h₃ (finite_setOf_homology_ne_zero (c := cL) (h := h₁) hnL) (by simp)
      (finite_setOf_homology_ne_zero (c := zeroBasis cK) (h := h₃) hnK_shift) α β γ
      sα hsα (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0) (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0)
      hm₁ (fun _ ↦ rfl) hm₃ (fun q ↦ ?_) (fun _ ↦ funext fun k ↦ k.elim0) (fun q ↦ ?_)
    · ext k
      obtain ⟨l, rfl⟩ := (finCongr (hm₁ q).symm).surjective k
      have hc' : Fin.cast (hm₁ q) ((finCongr (hm₁ q).symm) l) = l := Fin.ext (by simp)
      rw [Function.comp_apply, hc']
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.append_left, α, Basis.map_apply, LinearEquiv.ofTop_symm_apply]
        exact congrArg (h₁ q) (Fin.ext (by simp))
      | right l => exact l.elim0
    · ext k
      obtain ⟨l, rfl⟩ := (finCongr (hm₃ q).symm).surjective k
      have hc' : Fin.cast (hm₃ q) ((finCongr (hm₃ q).symm) l) = l := Fin.ext (by simp)
      rw [Function.comp_apply, hc']
      induction l using Fin.addCases with
      | left l => exact l.elim0
      | right l =>
        simp only [Fin.append_right, sα]
        exact congrArg (h₃ (q + 1)) (Fin.ext (by simp))
  have hmul := reidemeisterTorsion_eq_mul_of_shortExact_acyclic_X₂ hS hcone_ac cL (zeroBasis cK)
    (basis φ cK cL) (fun i k ↦ basis_castAdd φ cK cL i k) (fun i k ↦ by
      rw [basis_natAdd, zeroBasis_apply]
      have h₀ := inlX_mapArrowHom_f φ (0 : K ⟶ 0) hc (Arrow.homMk (𝟙 K) 0) (i - 1) i (by simp)
      have h := congr(($h₀).hom (cK (i - 1) k))
      simp only [Arrow.homMk_left, id_f] at h
      exact h) h₁ h₂ h₃
  rw [hmul, hH₁, mul_one, hshift]
  simp only [hq]
  have hε := finprod_mul_distrib
    (hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hnK fun j ↦
      finrank F (LinearMap.range (L.d (j + 1) j).hom))
    (hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hnK fun _ ↦ 1)
  simp only [mul_one, ← pow_add, ← mul_add_one] at hε
  rw [hε]
  ring

open homotopyCofiber in
/-- **The torsion with transported homology bases under a quasi-isomorphism.** If `φ : K ⟶ L` is a
quasi-isomorphism of based complexes with `K` bounded and `hK` is a family of homology bases of `K`,
then

`τ(L, cL, φ_* hK) = ε · τ(cone φ) · τ(K, cK, hK)`

with `ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))`. -/
theorem reidemeisterTorsionWithHomology_map_eq_mul_of_quasiIso
    {K L : ChainComplex (ModuleCat F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    {nK nL m : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) F (K.X i))
    (cL : ∀ i, Basis (Fin (nL i)) F (L.X i))
    (hK : ∀ i, Basis (Fin (m i)) F (K.homology i)) (hn : {i | nK i ≠ 0}.Finite) :
    L.reidemeisterTorsionWithHomology cL
        (fun i ↦ (hK i).map (isoOfQuasiIsoAt φ i).toLinearEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      ((homotopyCofiber φ).reidemeisterTorsion (basis φ cK cL) *
        K.reidemeisterTorsionWithHomology cK hK) := by
  have hsupp := hasFiniteMulSupport_neg_one_pow_finrank_mul K cK hn fun j ↦
    finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1
  have hε : (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
      (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) = 1 := by
    rw [← finprod_mul_distrib hsupp hsupp]
    simp [← mul_pow]
  rw [reidemeisterTorsion_homotopyCofiber_of_quasiIso φ cK cL hK]
  simp [← mul_assoc, hε, reidemeisterTorsionWithHomology_ne_zero (c := cK) (h := hK) hn]

open homotopyCofiber in
/-- **The torsion with based homology under a quasi-isomorphism.** Let `φ : K ⟶ L` be a
quasi-isomorphism of based complexes with `K` bounded, and let `hK` and `hL` be homology bases of
`K` and `L`. Then

`τ(L, cL, hL) = ε · τ(cone φ) · τ(K, cK, hK) · ∏ᵢ det (Aᵢ) ^ ((-1) ^ i)`

where `Aᵢ` is the matrix of `Hᵢ(φ) : Hᵢ(K) → Hᵢ(L)` in the bases `hK i` and `hL i`, and
`ε = ∏ⱼ (-1) ^ (dim B(K)ⱼ · (dim B(L)ⱼ + 1))`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_quasiIso
    {K L : ChainComplex (ModuleCat F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    {nK nL m : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) F (K.X i))
    (cL : ∀ i, Basis (Fin (nL i)) F (L.X i))
    (hK : ∀ i, Basis (Fin (m i)) F (K.homology i))
    (hL : ∀ i, Basis (Fin (m i)) F (L.homology i)) (hn : {i | nK i ≠ 0}.Finite) :
    L.reidemeisterTorsionWithHomology cL hL =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (K.d (j + 1) j).hom) *
        (finrank F (LinearMap.range (L.d (j + 1) j).hom) + 1))) *
      ((homotopyCofiber φ).reidemeisterTorsion (basis φ cK cL) *
        K.reidemeisterTorsionWithHomology cK hK *
        ∏ᶠ i : ℤ,
          (LinearMap.toMatrix (hK i) (hL i) (homologyMap φ i).hom).det ^ (i.negOnePow : ℤ)) := by
  let hL' (i : ℤ) := (hK i).map (isoOfQuasiIsoAt φ i).toLinearEquiv
  rw [reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := cL) (h := hL') hL,
    reidemeisterTorsionWithHomology_map_eq_mul_of_quasiIso φ cK cL hK hn]
  have hdet (i : ℤ) : (hL' i).det (hL i) ^ ((i + 1).negOnePow : ℤ) =
      (LinearMap.toMatrix (hK i) (hL i) (homologyMap φ i).hom).det ^ (i.negOnePow : ℤ) := by
    have hinv : (hL' i).det (hL i) = ((hL i).det (hL' i))⁻¹ :=
      eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
    have hmat : (hL i).det (hL' i) =
        (LinearMap.toMatrix (hK i) (hL i) (homologyMap φ i).hom).det := by
      rw [Basis.det_apply]
      congr 2
      ext k
      simp [hL', Iso.toLinearEquiv_apply]
    rw [hinv, hmat, Int.negOnePow_succ, Units.val_neg, zpow_neg, inv_zpow, inv_inv]
  rw [finprod_congr hdet]
  ring

end MappingCone

end HomologicalComplex
