/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
import Mathlib.Algebra.Module.PID
import TauCeti.Algebra.Module.LocalizedModule.CoprimeTorsion
import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# Mod-`p` acyclicity of `K(A, 1)` for uniquely `p`-divisible `A`

Let `p` be a prime and let `A` be a module over `ℤ[1/p] = Localization.Away p`, equivalently an
abelian group on which multiplication by `p` is bijective. Then the classifying space
`K(A, 1) = B(Multiplicative A)` has the mod-`p` homology of a point: its singular homology with
coefficients in `𝔽_p` vanishes in every positive degree. More generally this holds with
coefficients in any commutative semisimple ring `k` in which `p = 0`. Equivalently, the group
homology of `A` with trivial coefficients `k` vanishes in positive degrees.

The proof reduces to finitely generated `ℤ[1/p]`-modules:

* every class of the group homology of `A` comes from a finitely generated `ℤ[1/p]`-submodule,
  since `A` is the directed union of these
  (`TauCeti.groupHomology.isZero_groupHomology_of_directed`);
* `ℤ[1/p]` is a principal ideal domain (`IsLocalization.isPrincipalIdealRing`), so a finitely
  generated `ℤ[1/p]`-module is a product of a free module `ℤ[1/p]ⁿ` and a torsion module
  (`Module.equiv_free_prod_directSum`), and the Künneth formula over `k` reduces to the factors
  (`TauCeti.subsingleton_groupHomology_prod`);
* `ℤ[1/p]` itself is acyclic: as the directed union of the infinite cyclic groups `p⁻ʳ ℤ` it has
  no homology in degrees at least two, and its first homology `ℤ[1/p] ⊗ k` vanishes since
  `ℤ[1/p]` is `p`-divisible (`TauCeti.isZero_groupHomology_localizationAway`,
  `TauCeti.isZero_groupHomology_one_localizationAway`);
* the torsion module is a finite group of order prime to `p`
  (`TauCeti.LocalizationAway.coprime_natCard_of_smul_eq_zero`), and the positive-degree homology
  of a finite group is killed by its order (`groupHomology.subsingleton_of_isUnit_natCard`), which
  is a unit of `k`.

For `p = 2` this is the input from Eilenberg–MacLane spaces of type `K(A, 1)` to the mod-two
Hurewicz theorem: a simply connected space with vanishing reduced mod-two homology has uniquely
two-divisible homotopy groups.

## Main results

* `TauCeti.subsingleton_groupHomology_of_natCast_eq_zero`: the group homology of a
  `ℤ[1/p]`-module with trivial coefficients `k`, `p = 0` in `k`, vanishes in positive degrees.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_natCast_eq_zero`: the same for the
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

/-- The free `ℤ[1/m]`-module `ℤ[1/m]ʳ` has no homology in positive degrees with coefficients in a
semisimple ring in which `m = 0`. -/
theorem subsingleton_groupHomology_pi_localizationAway [IsSemisimpleRing k] {m : ℤ} (hm : m ≠ 0)
    (hk : (m : k) = 0) (r n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Fin r → Localization.Away m)) k) (n + 1)) := by
  induction r generalizing n with
  | zero =>
    exact ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton _ n)
  | succ r ih =>
    have := subsingleton_groupHomology_prod _ _ k
      (subsingleton_groupHomology_localizationAway k hm hk) ih n
    exact groupHomology.subsingleton_groupHomology_of_mulEquiv (B := Rep.trivial k _ k)
      ((Fin.consLinearEquiv ℤ fun _ ↦ Localization.Away m).symm.toAddEquiv.toMultiplicative
        |>.trans (MulEquiv.prodMultiplicative _ _)) (.refl k k) (n + 1)

variable {p : ℕ}

/-- For a prime `p`, a finitely generated `ℤ[1/p]`-module killed by a nonzero element of `ℤ[1/p]`
has no homology in positive degrees with coefficients in which `p = 0`: it is a finite group of
order prime to `p`. -/
theorem subsingleton_groupHomology_of_natCast_eq_zero_of_smul_eq_zero (hp : p.Prime)
    (hk : (p : k) = 0) {T : Type} [AddCommGroup T] [Module (Localization.Away (p : ℤ)) T]
    [Module.Finite (Localization.Away (p : ℤ)) T] {x : Localization.Away (p : ℤ)} (hx : x ≠ 0)
    (hT : ∀ t : T, x • t = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative T) k) (n + 1)) := by
  have := LocalizationAway.finite_of_smul_eq_zero hp hx hT
  refine groupHomology.subsingleton_of_isUnit_natCard _ ?_ n
  rw [Nat.card_congr Multiplicative.toAdd]
  -- `p` and the order of `T` are coprime, and `p = 0` in `k`.
  simpa [hk, isCoprime_zero_left] using (Nat.isCoprime_iff_coprime.2
    (LocalizationAway.coprime_natCard_of_smul_eq_zero hp hx hT)).map (Int.castRingHom k)

/-- A `ℤ[1/p]`-module which is the product of a free module `ℤ[1/p]ʳ` and a finitely generated
module killed by a nonzero element has no homology in positive degrees with coefficients in a
semisimple ring in which `p = 0`. -/
private theorem subsingleton_groupHomology_of_linearEquiv_prod [IsSemisimpleRing k]
    (hp : p.Prime) (hk : (p : k) = 0) {N T : Type} [AddCommGroup N]
    [Module (Localization.Away (p : ℤ)) N] [AddCommGroup T] [Module (Localization.Away (p : ℤ)) T]
    [Module.Finite (Localization.Away (p : ℤ)) T] {r : ℕ}
    (f : N ≃ₗ[Localization.Away (p : ℤ)] (Fin r →₀ Localization.Away (p : ℤ)) × T)
    {x : Localization.Away (p : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  have := subsingleton_groupHomology_prod _ _ k
    (subsingleton_groupHomology_pi_localizationAway (Int.natCast_ne_zero.2 hp.ne_zero)
      (by exact_mod_cast hk) r)
    (subsingleton_groupHomology_of_natCast_eq_zero_of_smul_eq_zero hp hk hx hT) n
  exact groupHomology.subsingleton_groupHomology_of_mulEquiv (B := Rep.trivial k _ k)
    (((f.trans ((Finsupp.linearEquivFunOnFinite _ _ _).prodCongr (LinearEquiv.refl _ _))).toAddEquiv
      |>.toMultiplicative).trans (MulEquiv.prodMultiplicative _ _)) (.refl k k) (n + 1)

/-- For a prime `p`, a finitely generated `ℤ[1/p]`-module has no homology in positive degrees with
coefficients in a semisimple ring in which `p = 0`. -/
theorem subsingleton_groupHomology_of_natCast_eq_zero_of_moduleFinite [IsSemisimpleRing k]
    (hp : p.Prime) (hk : (p : k) = 0) {N : Type} [AddCommGroup N]
    [Module (Localization.Away (p : ℤ)) N] [Module.Finite (Localization.Away (p : ℤ)) N] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  classical
  have := IsLocalization.isPrincipalIdealRing (Submonoid.powers (p : ℤ))
    (Localization.Away (p : ℤ))
  have : IsDomain (Localization.Away (p : ℤ)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.natCast_ne_zero.2 hp.ne_zero))
  -- The structure theorem over the principal ideal domain `ℤ[1/p]`.
  obtain ⟨r, ι, _, q, hq, e, ⟨f⟩⟩ :=
    Module.equiv_free_prod_directSum (Localization.Away (p : ℤ)) N
  have : Module.Finite (Localization.Away (p : ℤ))
      (⨁ i : ι, Localization.Away (p : ℤ) ⧸ Localization.Away (p : ℤ) ∙ q i ^ e i) :=
    Module.Finite.of_surjective ((LinearMap.snd _ _ _).comp f.toLinearMap)
      fun t ↦ ⟨f.symm (0, t), by simp⟩
  -- The torsion part is killed by the product of the prime powers.
  refine subsingleton_groupHomology_of_linearEquiv_prod hp hk f (x := ∏ i, q i ^ e i)
    (Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero (e i) (hq i).ne_zero) (fun t ↦ ?_) n
  ext i
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (t i)
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j ↦ q j ^ e j) (Finset.mem_univ i)
  simp only [DirectSum.smul_apply, DirectSum.zero_apply, ← ha, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  exact ⟨c * a, by rw [hc, smul_eq_mul, smul_eq_mul]; ring⟩

/-- **The group homology of a `ℤ[1/p]`-module vanishes modulo `p`.** For a prime `p`, a module `A`
over `ℤ[1/p]` and a commutative semisimple ring `k` in which `p = 0`, such as `𝔽_p`, the group
homology of the additive group of `A` with trivial coefficients `k` vanishes in every positive
degree. -/
theorem subsingleton_groupHomology_of_natCast_eq_zero [IsSemisimpleRing k] (hp : p.Prime)
    (hk : (p : k) = 0) (A : Type) [AddCommGroup A] [Module (Localization.Away (p : ℤ)) A]
    (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) := by
  -- `A` is the directed union of its finitely generated `ℤ[1/p]`-submodules.
  let S : Finset A → Subgroup (Multiplicative A) := fun s ↦
    (Submodule.span (Localization.Away (p : ℤ)) (s : Set A)).toAddSubgroup.toSubgroup
  have hS : Directed (· ≤ ·) S := Monotone.directed_le fun s t hst ↦
    AddSubgroup.toSubgroup.monotone (Submodule.span_mono (Finset.coe_subset.2 hst))
  have hG : ⨆ s, S s = ⊤ := eq_top_iff.2 fun g _ ↦
    Subgroup.mem_iSup_of_mem {g.toAdd}
      ((Multiplicative.mem_toSubgroup _ _).2 (Submodule.subset_span (by simp)))
  rw [← ModuleCat.isZero_iff_subsingleton]
  refine TauCeti.groupHomology.isZero_groupHomology_of_directed hS hG fun s ↦ ?_
  -- The subgroup `S s` is the image of the additive group of the submodule `N = span s`.
  let N := Submodule.span (Localization.Away (p : ℤ)) (s : Set A)
  let φ : Multiplicative N →* Multiplicative A := N.subtype.toAddMonoidHom.toMultiplicative
  have hφ : S s = MonoidHom.range (G := Multiplicative N) φ := by
    ext g
    rw [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup, MonoidHom.mem_range]
    refine ⟨fun hg ↦ ⟨Multiplicative.ofAdd ⟨g.toAdd, hg⟩, rfl⟩, ?_⟩
    rintro ⟨x, rfl⟩
    exact x.toAdd.2
  let e : Multiplicative N ≃* S s :=
    (MonoidHom.ofInjective (G := Multiplicative N) (f := φ)
      fun _ _ h ↦ Subtype.val_injective h).trans (MulEquiv.subgroupCongr hφ).symm
  have := subsingleton_groupHomology_of_natCast_eq_zero_of_moduleFinite hp hk (k := k) (N := N) n
  exact ModuleCat.isZero_iff_subsingleton.2
    (groupHomology.subsingleton_groupHomology_of_mulEquiv (G := S s) (H := Multiplicative N)
      (B := Rep.trivial k (Multiplicative N) k) e.symm (.refl k k) (n + 1))

/-- **`K(A, 1)` is acyclic modulo `p` for a `ℤ[1/p]`-module `A`.** For a prime `p`, a module `A`
over `ℤ[1/p]` and a commutative semisimple ring `k` in which `p = 0`, such as `𝔽_p`, the singular
homology of the classifying space `K(A, 1) = B(Multiplicative A)` with coefficients in `k` vanishes
in every positive degree. -/
theorem subsingleton_classifyingSpace_singularHomology_of_natCast_eq_zero [IsSemisimpleRing k]
    (hp : p.Prime) (hk : (p : k) = 0) (A : Type) [AddCommGroup A]
    [Module (Localization.Away (p : ℤ)) A] (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_natCast_eq_zero hp hk A n
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
  subsingleton_classifyingSpace_singularHomology_of_natCast_eq_zero (p := 2) Nat.prime_two
    (by exact_mod_cast hk) A n

end TauCeti
