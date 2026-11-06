/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.RepresentationTheory.Homological.GroupHomology.DirectedUnion
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
import Mathlib.Algebra.Module.PID
import TauCeti.Algebra.Module.LocalizedModule.OddTorsion
import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# Mod-two acyclicity of `K(A, 1)` for uniquely two-divisible `A`

Let `A` be a module over `ℤ[1/2] = Localization.Away 2`, equivalently an abelian group on which
multiplication by two is bijective. Then the classifying space `K(A, 1) = B(Multiplicative A)` has
the mod-two homology of a point: its singular homology with coefficients in `𝔽₂` vanishes in
every positive degree. More generally this holds with coefficients in any commutative semisimple
ring `k` in which `2 = 0`. Equivalently, the group homology of `A` with trivial coefficients `k`
vanishes in positive degrees.

The proof reduces to finitely generated `ℤ[1/2]`-modules:

* every class of the group homology of `A` comes from a finitely generated `ℤ[1/2]`-submodule,
  since `A` is the directed union of these
  (`TauCeti.groupHomology.isZero_groupHomology_of_directed`);
* `ℤ[1/2]` is a principal ideal domain (`IsLocalization.isPrincipalIdealRing`), so a finitely
  generated `ℤ[1/2]`-module is a product of a free module `ℤ[1/2]ⁿ` and a torsion module
  (`Module.equiv_free_prod_directSum`), and the Künneth formula over `k` reduces to the factors
  (`TauCeti.subsingleton_groupHomology_prod`);
* `ℤ[1/2]` itself is acyclic: as the directed union of the infinite cyclic groups `2⁻ʳ ℤ` it has
  no homology in degrees at least two, and its first homology `ℤ[1/2] ⊗ k` vanishes since
  `ℤ[1/2]` is two-divisible (`TauCeti.isZero_groupHomology_localizationAway`,
  `TauCeti.isZero_groupHomology_one_localizationAway`);
* the torsion module is a finite group of odd order
  (`TauCeti.LocalizationAwayTwo.odd_natCard_of_smul_eq_zero`), and the positive-degree homology of
  a finite group is killed by its order (`groupHomology.subsingleton_of_isUnit_natCard`), which is
  a unit of `k`.

This is the input from Eilenberg–MacLane spaces of type `K(A, 1)` to the mod-two Hurewicz theorem:
a simply connected space with vanishing reduced mod-two homology has uniquely two-divisible
homotopy groups.

## Main results

* `TauCeti.subsingleton_groupHomology_of_two_eq_zero`: the group homology of a `ℤ[1/2]`-module
  with trivial coefficients `k`, `2 = 0` in `k`, vanishes in positive degrees.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_two_eq_zero`: the same for the
  singular homology of `K(A, 1)`.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`: `K(A, 1)` has
  the mod-two homology of a point for every uniquely two-divisible abelian group `A`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter III, Proposition 10.1, and Chapter V, Proposition 5.3.
-/

public section

open CategoryTheory Limits groupHomology DirectSum

namespace TauCeti

variable {k : Type} [CommRing k]

/-- The additive group of `ℤ[1/2]` has no homology in positive degrees with coefficients in which
`2 = 0`. -/
theorem subsingleton_groupHomology_localizationAway_two (hk : (2 : k) = 0) (n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Localization.Away (2 : ℤ))) k) (n + 1)) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  rcases n with _ | n
  · exact isZero_groupHomology_one_localizationAway k (by simpa using hk)
  · exact isZero_groupHomology_localizationAway k two_ne_zero (by omega)

/-- The free `ℤ[1/2]`-module `ℤ[1/2]ⁿ` has no homology in positive degrees with coefficients in a
semisimple ring in which `2 = 0`. -/
theorem subsingleton_groupHomology_fin_localizationAway_two [IsSemisimpleRing k] (hk : (2 : k) = 0)
    (r n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Fin r → Localization.Away (2 : ℤ))) k)
        (n + 1)) := by
  induction r generalizing n with
  | zero =>
    exact ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton _ n)
  | succ r ih =>
    let e : Multiplicative (Fin (r + 1) → Localization.Away (2 : ℤ)) ≃*
        Multiplicative (Localization.Away (2 : ℤ)) ×
          Multiplicative (Fin r → Localization.Away (2 : ℤ)) :=
      (Fin.consLinearEquiv ℤ fun _ ↦ Localization.Away (2 : ℤ)).symm.toAddEquiv.toMultiplicative
        |>.trans (MulEquiv.prodMultiplicative _ _)
    have := subsingleton_groupHomology_prod _ _ k
      (subsingleton_groupHomology_localizationAway_two hk) ih n
    exact (groupHomology.mapIso (A := Rep.trivial k _ k) (B := Rep.trivial k _ k) e
      (LinearEquiv.refl k k) (fun _ ↦ by ext; simp) (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- A finitely generated `ℤ[1/2]`-module killed by a nonzero element of `ℤ[1/2]` has no homology
in positive degrees with coefficients in which `2 = 0`: it is a finite group of odd order. -/
theorem subsingleton_groupHomology_of_smul_eq_zero (hk : (2 : k) = 0) {T : Type}
    [AddCommGroup T] [Module (Localization.Away (2 : ℤ)) T]
    [Module.Finite (Localization.Away (2 : ℤ)) T] {x : Localization.Away (2 : ℤ)} (hx : x ≠ 0)
    (hT : ∀ t : T, x • t = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative T) k) (n + 1)) := by
  have := LocalizationAwayTwo.finite_of_smul_eq_zero hx hT
  refine groupHomology.subsingleton_of_isUnit_natCard _ ?_ n
  obtain ⟨a, ha⟩ := LocalizationAwayTwo.odd_natCard_of_smul_eq_zero hx hT
  rw [show Nat.card (Multiplicative T) = Nat.card T from Nat.card_congr Multiplicative.toAdd, ha]
  simp [hk]

/-- A `ℤ[1/2]`-module which is the product of a free module `ℤ[1/2]ʳ` and a finitely generated
module killed by a nonzero element has no homology in positive degrees with coefficients in a
semisimple ring in which `2 = 0`. -/
private theorem subsingleton_groupHomology_of_linearEquiv_prod [IsSemisimpleRing k]
    (hk : (2 : k) = 0) {N T : Type} [AddCommGroup N] [Module (Localization.Away (2 : ℤ)) N]
    [AddCommGroup T] [Module (Localization.Away (2 : ℤ)) T]
    [Module.Finite (Localization.Away (2 : ℤ)) T] {r : ℕ}
    (f : N ≃ₗ[Localization.Away (2 : ℤ)] (Fin r →₀ Localization.Away (2 : ℤ)) × T)
    {x : Localization.Away (2 : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  let g : Multiplicative N ≃*
      Multiplicative (Fin r → Localization.Away (2 : ℤ)) × Multiplicative T :=
    ((f.trans ((Finsupp.linearEquivFunOnFinite _ _ _).prodCongr (LinearEquiv.refl _ _))).toAddEquiv
      |>.toMultiplicative).trans (MulEquiv.prodMultiplicative _ _)
  have := subsingleton_groupHomology_prod _ _ k
    (subsingleton_groupHomology_fin_localizationAway_two hk r)
    (subsingleton_groupHomology_of_smul_eq_zero hk hx hT) n
  exact (groupHomology.mapIso (A := Rep.trivial k _ k) (B := Rep.trivial k _ k) g
    (LinearEquiv.refl k k) (fun _ ↦ by ext; simp) (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- A finitely generated `ℤ[1/2]`-module has no homology in positive degrees with coefficients in a
semisimple ring in which `2 = 0`. -/
theorem subsingleton_groupHomology_of_finite [IsSemisimpleRing k] (hk : (2 : k) = 0) {N : Type}
    [AddCommGroup N] [Module (Localization.Away (2 : ℤ)) N]
    [Module.Finite (Localization.Away (2 : ℤ)) N] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  classical
  have := IsLocalization.isPrincipalIdealRing (Submonoid.powers (2 : ℤ))
    (Localization.Away (2 : ℤ))
  have : IsDomain (Localization.Away (2 : ℤ)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)
  -- The structure theorem over the principal ideal domain `ℤ[1/2]`.
  obtain ⟨r, ι, _, p, hp, e, ⟨f⟩⟩ :=
    Module.equiv_free_prod_directSum (Localization.Away (2 : ℤ)) N
  have : Module.Finite (Localization.Away (2 : ℤ))
      (⨁ i : ι, Localization.Away (2 : ℤ) ⧸ Localization.Away (2 : ℤ) ∙ p i ^ e i) :=
    Module.Finite.of_surjective ((LinearMap.snd _ _ _).comp f.toLinearMap)
      fun t ↦ ⟨f.symm (0, t), by simp⟩
  -- The torsion part is killed by the product of the prime powers.
  refine subsingleton_groupHomology_of_linearEquiv_prod hk f (x := ∏ i, p i ^ e i)
    (Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero (e i) (hp i).ne_zero) (fun t ↦ ?_) n
  ext i
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (t i)
  rw [DirectSum.smul_apply, DirectSum.zero_apply, ← ha,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ← Submodule.Quotient.mk_smul,
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton.2 ⟨a, by simp [mul_comm]⟩),
    smul_zero]

/-- **The group homology of a `ℤ[1/2]`-module vanishes modulo two.** For a module `A` over
`ℤ[1/2]` and a commutative semisimple ring `k` in which `2 = 0`, such as `𝔽₂`, the group homology
of the additive group of `A` with trivial coefficients `k` vanishes in every positive degree. -/
theorem subsingleton_groupHomology_of_two_eq_zero [IsSemisimpleRing k] (hk : (2 : k) = 0)
    (A : Type) [AddCommGroup A] [Module (Localization.Away (2 : ℤ)) A] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) := by
  -- `A` is the directed union of its finitely generated `ℤ[1/2]`-submodules.
  let S : Finset A → Subgroup (Multiplicative A) := fun s ↦
    (Submodule.span (Localization.Away (2 : ℤ)) (s : Set A)).toAddSubgroup.toSubgroup
  have hS : Directed (· ≤ ·) S := Monotone.directed_le fun s t hst ↦
    AddSubgroup.toSubgroup.monotone (Submodule.span_mono (Finset.coe_subset.2 hst))
  have hG : ⨆ s, S s = ⊤ := eq_top_iff.2 fun g _ ↦
    Subgroup.mem_iSup_of_mem {g.toAdd}
      ((Multiplicative.mem_toSubgroup _ _).2 (Submodule.subset_span (by simp)))
  rw [← ModuleCat.isZero_iff_subsingleton]
  refine TauCeti.groupHomology.isZero_groupHomology_of_directed hS hG fun s ↦ ?_
  -- The subgroup `S s` is the additive group of the finitely generated submodule `span s`.
  have := subsingleton_groupHomology_of_finite hk
    (N := Submodule.span (Localization.Away (2 : ℤ)) (s : Set A)) n
  refine (@ModuleCat.isZero_of_subsingleton _ _ _ this).of_iso
    (groupHomology.mapIso
      { toFun x := ⟨Multiplicative.ofAdd (x.toAdd : A), x.toAdd.2⟩
        invFun g := Multiplicative.ofAdd ⟨g.1.toAdd, g.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl } (LinearEquiv.refl k k) (fun _ ↦ ?_) (n + 1)).symm
  ext
  simp

/-- **`K(A, 1)` is acyclic modulo two for a `ℤ[1/2]`-module `A`.** For a module `A` over
`ℤ[1/2]` and a commutative semisimple ring `k` in which `2 = 0`, such as `𝔽₂`, the singular
homology of the classifying space `K(A, 1) = B(Multiplicative A)` with coefficients in `k` vanishes
in every positive degree. -/
theorem subsingleton_classifyingSpace_singularHomology_of_two_eq_zero [IsSemisimpleRing k]
    (hk : (2 : k) = 0) (A : Type) [AddCommGroup A] [Module (Localization.Away (2 : ℤ)) A] (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_two_eq_zero hk A n
  (classifyingSpaceSingularHomologyIsoGroupHomology k (Multiplicative A) (n + 1)).toLinearEquiv
    |>.toEquiv.subsingleton

/-- **`K(A, 1)` has the mod-two homology of a point for uniquely two-divisible `A`.** If
multiplication by two is bijective on the abelian group `A`, then the singular homology of the
classifying space `K(A, 1) = B(Multiplicative A)` with coefficients in a commutative semisimple ring
`k` in which `2 = 0`, such as `𝔽₂`, vanishes in every positive degree. -/
theorem IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology {A : Type}
    [AddCommGroup A] [IsSemisimpleRing k] (h : IsUniquelyTwoDivisible A) (hk : (2 : k) = 0)
    (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  letI := h.localizationAwayTwoModule
  subsingleton_classifyingSpace_singularHomology_of_two_eq_zero hk A n

end TauCeti
