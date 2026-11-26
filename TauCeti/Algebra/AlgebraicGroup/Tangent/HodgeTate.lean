/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Convolution.Integral
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent.Relations
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Torsion
public import TauCeti.Algebra.Coalgebra.GroupLike.Finite
public import TauCeti.Algebra.Module.ValuationRing.Separation

/-!
# The finite flat Hodge–Tate cokernel bound at every prime

Let `C` be an algebraically closed ultrametric normed field and
`O` its valuation ring. For a finite flat commutative and cocommutative Hopf `O`-algebra,
every scalar `κ` satisfying `‖κ‖ ^ (p - 1) ≤ ‖p‖`, with `p` prime and `‖p‖ < 1`, multiplies
the cotangent space into the span of the displacements of group-like elements.
Neither completeness nor characteristic zero of `C`, nor a restriction on the rank, is
required. In particular the
bound includes `p = 2` with `κ = 2`.

## References

* L. Fargues, *La filtration de Harder–Narasimhan des schémas en groupes finis et plats*,
  J. reine angew. Math. 645 (2010), 1–39, §9, Théorème 7 (for odd primes),
  https://webusers.imj-prg.fr/~laurent.fargues/HNgp.pdf.
* L. Fargues, with Y. Tian, *La filtration canonique des points de torsion des groupes
  p-divisibles*, Ann. Sci. Éc. Norm. Supér. (4) 44 (2011), 905–961,
  §5.3.2, Théorème 2 and §5.4, Théorème 3,
  https://webusers.imj-prg.fr/~laurent.fargues/canoniqueHN.pdf.

The argument is due to L. Alpöge, from his formal Lean proof of the Riemann hypothesis
for Dirichlet L-functions (2026), https://github.com/leanprover-community/riemann-hypothesis;
the formalization here is independent of that source.
-/

public noncomputable section

open Coalgebra TensorProduct

namespace TauCeti.Bialgebra

section Relations

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

private def testModule (q : R) : Submodule R A :=
  Submodule.span R (Set.range (GroupLike.val : GroupLike R A → A)) ⊔
    LinearMap.range (cotangentRelation R A) ⊔ LinearMap.range (q • LinearMap.id)

private theorem smul_mem_testModule (q : R) (a : A) : q • a ∈ testModule (A := A) q :=
  Submodule.mem_sup_right ⟨a, rfl⟩

private theorem testModule_le_comap (q : R) (hq : ∀ x : CotangentSpace R A, q • x = 0) :
    testModule (A := A) q ≤ (Submodule.span R
      (Set.range fun u : GroupLike R A ↦ cotangentMap R A u.val)).comap (cotangentMap R A) := by
  refine sup_le (sup_le (Submodule.span_le.mpr ?_) ?_) ?_
  · rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨u, rfl⟩
  · rintro _ ⟨t, rfl⟩
    rw [Submodule.mem_comap, ← LinearMap.comp_apply,
      cotangentMap_comp_cotangentRelation, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · rintro _ ⟨a, rfl⟩
    simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul, hq] using (Submodule.zero_mem (Submodule.span R
        (Set.range fun u : GroupLike R A ↦ cotangentMap R A u.val)))

end Relations

section Bound

variable {C : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "O(" C ")" => Valuation.valuationSubring (NormedField.valuation (K := C))

variable {A : Type*} [CommRing A] [Bialgebra O(C) A] [Coalgebra.IsCocomm O(C) A]
  [Module.Finite O(C) A] [Module.Free O(C) A]

omit [IsAlgClosed C] [Coalgebra.IsCocomm O(C) A] in
private theorem testModule_fg (q : O(C)) : (testModule (A := A) q).FG :=
  ((Submodule.fg_span (Set.finite_range _)).sup (Submodule.fg_range _)).sup (Submodule.fg_range _)

private theorem factorialRadius_smul_mem_testModule
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) {q : O(C)} (hq : q ≠ 0)
    (κ : O(C)) (hκ : ‖(κ : C)‖ ^ (p - 1) ≤ ‖(p : C)‖) (a : A) :
    κ • a ∈ testModule (A := A) q := by
  apply ((testModule (A := A) q).mem_iff_forall_dvd_linearMap (testModule_fg q) hq
    (smul_mem_testModule q) (κ • a)).mpr
  intro D hD
  have hgroup (u : GroupLike O(C) A) : q ∣ D u.val :=
    hD _ (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span ⟨u, rfl⟩)))
  have hrel (b c : A) :
      q ∣ D (b * c) - counit c * D b - counit b * D c := by
    have h := hD _ (Submodule.mem_sup_left (Submodule.mem_sup_right
      (LinearMap.mem_range_self (cotangentRelation O(C) A) (b ⊗ₜ[O(C)] c))))
    simpa only [cotangentRelation_tmul, map_sub, map_smul, smul_eq_mul] using h
  simpa only [map_smul, smul_eq_mul] using
    WithConv.dvd_mul_apply_of_groupLike p hp hpC D hq hgroup hrel κ hκ a

/-- A nonzero annihilator of the cotangent space suffices for the factorial-radius bound
on a finite free commutative and cocommutative bialgebra over a valuation ring. -/
theorem smul_mem_span_cotangentMap_groupLike_of_annihilator
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) {q : O(C)} (hq : q ≠ 0)
    (hqω : ∀ x : CotangentSpace O(C) A, q • x = 0)
    (κ : O(C)) (hκ : ‖(κ : C)‖ ^ (p - 1) ≤ ‖(p : C)‖)
    (x : CotangentSpace O(C) A) :
    κ • x ∈ Submodule.span O(C)
      (Set.range fun u : GroupLike O(C) A ↦ cotangentMap O(C) A u.val) := by
  obtain ⟨a, rfl⟩ := cotangentMap_surjective O(C) A x
  rw [← map_smul]
  exact testModule_le_comap q hqω (factorialRadius_smul_mem_testModule p hp hpC hq κ hκ a)

end Bound

section Hopf

variable {C : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "O(" C ")" => Valuation.valuationSubring (NormedField.valuation (K := C))

/-- The finite flat Hodge–Tate cokernel bound at every prime, including `2`. The coordinate
Hopf algebra may have arbitrary finite rank, and the field need not be complete. -/
theorem smul_mem_span_cotangentMap_groupLike
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1)
    {A : Type*} [CommRing A] [HopfAlgebra O(C) A] [Coalgebra.IsCocomm O(C) A]
    [Module.Finite O(C) A] [Module.Flat O(C) A]
    (κ : O(C)) (hκ : ‖(κ : C)‖ ^ (p - 1) ≤ ‖(p : C)‖)
    (x : CotangentSpace O(C) A) :
    κ • x ∈ Submodule.span O(C)
      (Set.range fun u : GroupLike O(C) A ↦ cotangentMap O(C) A u.val) := by
  by_cases hp0 : (p : C) = 0
  · have hpow : ‖(κ : C)‖ ^ (p - 1) = 0 :=
      le_antisymm (by simpa only [hp0, norm_zero] using hκ) (by positivity)
    have hκ0 : κ = 0 := Subtype.ext (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hpow))
    simp [hκ0]
  have : CharZero C := NormedField.charZero_of_prime_norm_lt_one hp hpC hp0
  have : Module.Free O(C) A := Module.free_of_flat_of_isLocalRing
  have : Nontrivial A := _root_.Bialgebra.nontrivial O(C)
  have hq : (Module.finrank O(C) A : O(C)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := O(C)) (M := A)).ne'
  exact smul_mem_span_cotangentMap_groupLike_of_annihilator p hp hpC hq
    finrank_smul_cotangentSpace_eq_zero κ hκ x

end Hopf

end TauCeti.Bialgebra
