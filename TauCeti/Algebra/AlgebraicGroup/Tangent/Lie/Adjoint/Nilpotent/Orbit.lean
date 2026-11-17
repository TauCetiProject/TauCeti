/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Cone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
import Mathlib.Data.Set.Card
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Orbit

/-!
# Classification and finiteness of nilpotent adjoint orbits

Let `G = Spec H` be an affine group over a field `k` with finite-dimensional Lie algebra `𝔤`,
modelled as `Module.Dual k (Bialgebra.CotangentSpace k H)`. A rational adjoint orbit
`O ∈ Comodule.VectorOrbit k H 𝔤` is **nilpotent** (`TauCeti.nilpotentOrbits k H`) if its elements
`x ∈ 𝔤` have nilpotent adjoint endomorphism `ad x`; since `G(k)` acts by Lie automorphisms
(`Derivation.basePointsAdjointLieEquiv`), this is well-defined on orbits. The set of **nonzero
nilpotent orbits** is `TauCeti.nonzeroNilpotentOrbits k H`.

This file establishes the polynomial invariance, scaling cone property, finiteness, and weighted
Dynkin diagram classification of nilpotent adjoint orbits:

* **Invariance of polynomial evaluation**: every `G`-invariant polynomial `p ∈ O(𝔤)^G`
  (`TauCeti.adjointInvariantPolynomials k H`) is invariant under evaluation along the `G(k)`-action
  (`TauCeti.lift_eval_basePointsRepresentation_eq_of_mem_adjointInvariantPolynomials`). For
  connected `G` over an algebraically closed field of characteristic zero, the same holds for all
  Lie-invariant polynomials `p ∈ S(𝔤*)^𝔤`.
* **Scaling cone property**: when `𝔤` has nondegenerate Killing form, every `ad`-nilpotent element
  `e` is `G(k)`-conjugate to `c • e` for every `c : kˣ` (`TauCeti.mk_smul_eq_of_isNilpotent_ad`),
  using Jacobson–Morozov, `IsSl2Triple.rescale`, and openness of the grade-two centralizer orbit.
* **Finiteness (without connectedness)**: fixing a Cartan subalgebra `𝔥` and a base `b` of its root
  system, the map `b.orbitOfDominantNeutral` sends each dominant neutral element
  `h ∈ b.dominantNeutralElements` to the adjoint orbit of any `e` in an `sl₂` triple `(h, e, f)`.
  It is well-defined by openness of the grade-two centralizer orbit, and surjective onto
  `nonzeroNilpotentOrbits k H` via Jacobson–Morozov and the exponential realization of `Int(𝔤)`
  inside `G(k)`. Hence `nonzeroNilpotentOrbits k H` and `nilpotentOrbits k H` are finite, with
  `|nonzeroNilpotentOrbits| ≤ 3 ^ rank` and `|nilpotentOrbits| ≤ 3 ^ rank + 1`, with no
  connectedness hypothesis on `G`.
* **Weighted Dynkin diagram classification (connected `G`)**: when `G` is connected, `G(k)`
  preserves every Lie-invariant polynomial in `S(𝔤*)^𝔤`. Together with group-level Kostant
  conjugacy (`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_eq`), Chevalley restriction,
  and uniqueness of dominant representatives in Weyl orbits of integral coweights,
  `b.orbitOfDominantNeutral` is a bijection
  `b.dominantNeutralElements ≃ nonzeroNilpotentOrbits k H`.
  Its inverse composed with `b.weightedDynkinDiagram` defines an injective weighted Dynkin diagram
  `b.orbitWeightedDynkinDiagram : nonzeroNilpotentOrbits k H → (b.support → Fin 3)`, so two
  dominant `sl₂` triples have conjugate nilpositive elements if and only if they have the same
  weighted Dynkin diagram, and `|nilpotentOrbits| = |b.dominantNeutralElements| + 1`.

See `TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Closure` for closure stability,
minimality of the zero orbit, and the scheme-point decomposition of nilpotent orbit closures.

## Main declarations

* `TauCeti.lift_eval_basePointsRepresentation_eq_of_mem_adjointInvariantPolynomials` and
  `TauCeti.lift_eval_basePointsRepresentation_eq_of_mem_lieInvariants`
* `TauCeti.isNilpotent_ad_basePointsRepresentation_iff`
* `TauCeti.nilpotentOrbits`, `TauCeti.nonzeroNilpotentOrbits`
* `TauCeti.exists_basePointsRepresentation_smul_eq_of_isNilpotent_ad`,
  `TauCeti.mk_smul_eq_of_isNilpotent_ad`
* `RootPairing.Base.orbitOfDominantNeutral`, `RootPairing.Base.orbitOfDominantNeutral_eq_mk`,
  `RootPairing.Base.orbitOfDominantNeutral_surjective`
* `TauCeti.finite_nonzeroNilpotentOrbits`, `TauCeti.finite_nilpotentOrbits`,
  `TauCeti.ncard_nonzeroNilpotentOrbits_le`, `TauCeti.ncard_nilpotentOrbits_le`
* `RootPairing.Base.orbitOfDominantNeutral_injective`,
  `RootPairing.Base.orbitOfDominantNeutral_bijective`,
  `RootPairing.Base.nonzeroNilpotentOrbitsEquiv`,
  `RootPairing.Base.orbitWeightedDynkinDiagram`,
  `RootPairing.Base.orbitWeightedDynkinDiagram_injective`,
  `RootPairing.Base.mk_eq_mk_iff_weightedDynkinDiagram_eq`,
  `RootPairing.Base.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`,
  `RootPairing.Base.ncard_nonzeroNilpotentOrbits_eq`,
  `RootPairing.Base.ncard_nilpotentOrbits_eq`

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Chapter 3 (Theorems 3.2.10, 3.4.10, 3.5.4).
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Math. 228, Birkhäuser,
  2004, §3.
-/

public section

open CategoryTheory LieAlgebra LieAlgebra.IsKilling WithConv
open scoped TensorProduct

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

/-! ### Invariance of polynomial evaluation under rational points -/

section PolynomialInvariance

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Evaluation invariance for `G`-invariant polynomials.** Over any field `k`, evaluating a
`G`-invariant polynomial `p ∈ O(𝔤)^G` at `Ad(g) x` gives the same value as evaluating it at `x`.
No connectedness, algebraic-closure, or characteristic assumption is needed. -/
theorem lift_eval_basePointsRepresentation_eq_of_mem_adjointInvariantPolynomials
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H)
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤
        (Comodule.basePointsRepresentation (H := H) 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p := by
  let := Comodule.dual k H 𝔤
  let Φ : SymmetricAlgebra k (Module.Dual k 𝔤) ⊗[k] H →ₐ[k] k :=
    Algebra.TensorProduct.lift (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) g⁻¹.ofConv
      (fun _ _ ↦ Commute.all _ _)
  have heval : SymmetricAlgebra.lift (Module.Dual.eval k 𝔤
        (Comodule.basePointsRepresentation (H := H) 𝔤 g x)) =
      Φ.comp (Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext fun φ ↦ ?_
    simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply,
      Comodule.symmetricAlgebraCoact_ι]
    have hdual : φ (Comodule.basePointsRepresentation (H := H) 𝔤 g x) =
        Comodule.basePointsRepresentation (H := H) (Module.Dual k 𝔤) g⁻¹ φ x := by
      rw [Comodule.basePointsRepresentation_dual_apply, inv_inv]
    rw [hdual, Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, one_smul]
    generalize Comodule.coact (R := k) (C := H) φ = t
    induction t using TensorProduct.inductionOn with
    | tmul ψ h =>
      simp [Φ, Algebra.TensorProduct.lift_tmul, mul_comm]
    | add u v hu hv =>
      simp only [map_add, LinearMap.add_apply, hu, hv]
  have hcoact : Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤) p = p ⊗ₜ[k] (1 : H) := by
    let := adjointPolynomialComoduleAlgebra k H
    have hEq : ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤)) =
        Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤) := by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext fun φ ↦ ?_
      simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        ComoduleAlgebra.coactAlgHom_apply, adjointPolynomialComoduleAlgebra_coact_ι,
        Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]
    rw [← hEq, ComoduleAlgebra.coactAlgHom_apply]
    exact mem_adjointInvariantPolynomials.mp hp
  rw [AlgHom.congr_fun heval p, AlgHom.comp_apply, hcoact]
  simp [Φ, Algebra.TensorProduct.lift_tmul]

/-- **Evaluation invariance for Lie-invariant polynomials on a connected group.** For a connected
finite-type affine group over an algebraically closed field of characteristic zero, every
Lie-invariant polynomial `p ∈ S(𝔤*)^𝔤` takes the same value at `Ad(g) x` and `x`. -/
theorem lift_eval_basePointsRepresentation_eq_of_mem_lieInvariants [CharZero k] [IsAlgClosed k]
    [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤))
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤
        (Comodule.basePointsRepresentation (H := H) 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p := by
  have hp' : p ∈ adjointInvariantPolynomials k (FiniteTypeCommHopfAlgCat.of k H) := by
    rw [adjointInvariantPolynomials_eq_lieInvariants (H := FiniteTypeCommHopfAlgCat.of k H)]
    exact hp
  exact lift_eval_basePointsRepresentation_eq_of_mem_adjointInvariantPolynomials hp' g x

end PolynomialInvariance

/-! ### Nilpotent adjoint orbits: definitions and basic properties -/

section AdjointInvariance

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

local notation "𝔤" => Module.Dual R (Bialgebra.CotangentSpace R H)

/-- Acting by a rational point preserves `ad`-nilpotence, because `Ad(g)` is a Lie algebra
automorphism. Holds over any commutative ring `R`. -/
@[simp]
theorem isNilpotent_ad_basePointsRepresentation_iff (g : WithConv (H →ₐ[R] R)) (x : 𝔤) :
    IsNilpotent (LieAlgebra.ad R 𝔤 (Comodule.basePointsRepresentation (H := H) 𝔤 g x)) ↔
      IsNilpotent (LieAlgebra.ad R 𝔤 x) := by
  let φ := Derivation.basePointsAdjointLieEquiv (R := R) (H := H) g
  have hpow : ∀ (n : ℕ) (y : 𝔤),
      (LieAlgebra.ad R 𝔤 (Comodule.basePointsRepresentation (H := H) 𝔤 g x) ^ n) y =
        φ ((LieAlgebra.ad R 𝔤 x ^ n) (φ.symm y)) := by
    intro n
    induction n with
    | zero =>
      intro y
      simp
    | succ n ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp, ih,
        LieAlgebra.ad_apply, LieAlgebra.ad_apply, ← Derivation.basePointsAdjointLieEquiv_apply,
        ← LieEquiv.map_lie]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, LinearMap.ext fun y ↦ ?_⟩
    have hy := LinearMap.congr_fun hn (φ y)
    rw [hpow, LieEquiv.symm_apply_apply, LinearMap.zero_apply] at hy
    exact φ.injective (hy.trans (map_zero φ).symm)
  · rintro ⟨n, hn⟩
    refine ⟨n, LinearMap.ext fun y ↦ ?_⟩
    rw [hpow, hn, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end AdjointInvariance

section Definitions

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The set of **nilpotent adjoint orbits** of `G = Spec H`: rational adjoint orbits consisting of
`ad`-nilpotent elements of `𝔤`. -/
noncomputable def nilpotentOrbits : Set (Comodule.VectorOrbit k H 𝔤) :=
  Comodule.VectorOrbit.mk '' {x : 𝔤 | IsNilpotent (LieAlgebra.ad k 𝔤 x)}

/-- The set of **nonzero nilpotent adjoint orbits** of `G = Spec H`: nilpotent orbits other than
the zero orbit `Comodule.VectorOrbit.mk 0`. -/
noncomputable def nonzeroNilpotentOrbits : Set (Comodule.VectorOrbit k H 𝔤) :=
  {O ∈ nilpotentOrbits k H | O ≠ Comodule.VectorOrbit.mk (0 : 𝔤)}

variable {k H}

/-- The orbit of `x` is nilpotent if and only if `ad x` is nilpotent. -/
@[simp]
theorem mem_nilpotentOrbits_mk_iff {x : 𝔤} :
    (Comodule.VectorOrbit.mk x : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentOrbits k H ↔
      IsNilpotent (LieAlgebra.ad k 𝔤 x) := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨g, rfl⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp hyx
    exact (isNilpotent_ad_basePointsRepresentation_iff g y).mpr hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The orbit of `x` is a nonzero nilpotent orbit if and only if `ad x` is nilpotent and `x ≠ 0`. -/
@[simp]
theorem mem_nonzeroNilpotentOrbits_mk_iff {x : 𝔤} :
    (Comodule.VectorOrbit.mk x : Comodule.VectorOrbit k H 𝔤) ∈ nonzeroNilpotentOrbits k H ↔
      IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ x ≠ 0 := by
  simp [nonzeroNilpotentOrbits]

/-- The zero orbit is nilpotent. -/
theorem mk_zero_mem_nilpotentOrbits :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentOrbits k H := by
  rw [mem_nilpotentOrbits_mk_iff, map_zero]
  exact IsNilpotent.zero

/-- The zero orbit is not a nonzero nilpotent orbit. -/
theorem mk_zero_notMem_nonzeroNilpotentOrbits :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ∉
      nonzeroNilpotentOrbits k H := by
  simp [nonzeroNilpotentOrbits]

/-- Nonzero nilpotent orbits are nilpotent orbits. -/
theorem nonzeroNilpotentOrbits_subset_nilpotentOrbits :
    nonzeroNilpotentOrbits k H ⊆ nilpotentOrbits k H :=
  fun _ h ↦ h.1

/-- The set of all nilpotent orbits is obtained by inserting the zero orbit into the nonzero
nilpotent orbits. -/
theorem nilpotentOrbits_eq_insert_zero :
    nilpotentOrbits k H =
      insert (Comodule.VectorOrbit.mk (0 : 𝔤)) (nonzeroNilpotentOrbits k H) := by
  ext O
  by_cases h : O = Comodule.VectorOrbit.mk (0 : 𝔤)
  · subst h
    simp
  · simp [nonzeroNilpotentOrbits, h]

/-- In a trivial (rank-zero) Lie algebra, the only nilpotent orbit is the zero orbit. -/
theorem nilpotentOrbits_eq_singleton_of_subsingleton [Subsingleton 𝔤] :
    nilpotentOrbits k H = {Comodule.VectorOrbit.mk (0 : 𝔤)} := by
  ext O
  induction O using Comodule.VectorOrbit.ind with | h x
  rw [Subsingleton.elim x 0]
  simp

/-- A trivial (rank-zero) Lie algebra has no nonzero nilpotent orbits. -/
theorem nonzeroNilpotentOrbits_eq_empty_of_subsingleton [Subsingleton 𝔤] :
    nonzeroNilpotentOrbits k H = ∅ := by
  ext O
  induction O using Comodule.VectorOrbit.ind with | h x
  rw [Subsingleton.elim x 0]
  simp

/-- A trivial (rank-zero) Lie algebra has exactly one nilpotent orbit. -/
theorem ncard_nilpotentOrbits_of_subsingleton [Subsingleton 𝔤] :
    (nilpotentOrbits k H).ncard = 1 := by
  rw [nilpotentOrbits_eq_singleton_of_subsingleton, Set.ncard_singleton]

end Definitions

/-! ### Scaling cone property -/

section Scaling

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Scaling invariance of nilpotent elements.** When `𝔤` has nondegenerate Killing form over an
algebraically closed field of characteristic zero, every `ad`-nilpotent element `e` is conjugate
under `G(k)` to `c • e` for every unit `c : kˣ`. No connectedness hypothesis is needed. -/
theorem exists_basePointsRepresentation_smul_eq_of_isNilpotent_ad [IsKilling k 𝔤]
    {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (c : kˣ) :
    ∃ g : WithConv (H →ₐ[k] k),
      Comodule.basePointsRepresentation (H := H) 𝔤 g e = (c : k) • e := by
  by_cases he0 : e = 0
  · subst he0
    exact ⟨1, by simp⟩
  · obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
    obtain ⟨g, -, -, hge, -⟩ :=
      t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq
        (t.rescale c)
    exact ⟨g, hge⟩

/-- **Nilpotent orbits are cones.** Rescaling an `ad`-nilpotent element by a nonzero scalar does
not change its adjoint orbit. -/
theorem mk_smul_eq_of_isNilpotent_ad [IsKilling k 𝔤] {e : 𝔤}
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (c : kˣ) :
    (Comodule.VectorOrbit.mk ((c : k) • e) : Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk e := by
  obtain ⟨g, hg⟩ := exists_basePointsRepresentation_smul_eq_of_isNilpotent_ad he c
  exact (Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hg⟩).symm

end Scaling

end TauCeti

/-! ### Dominant neutral elements, finiteness, and weighted Dynkin diagram classification -/

namespace RootPairing.Base

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Surjectivity

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
  (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- Every nonzero `ad`-nilpotent element is `G(k)`-conjugate to the nilpositive element of an `sl₂`
triple whose neutral element is dominant for `b`. No connectedness hypothesis on `G` is needed. -/
theorem exists_basePointsRepresentation_isSl2Triple_mem_dominantNeutralElements
    {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (he0 : e ≠ 0) :
    ∃ g : WithConv (H →ₐ[k] k), ∃ h ∈ b.dominantNeutralElements, ∃ f : 𝔤,
      IsSl2Triple (h : 𝔤) (Comodule.basePointsRepresentation (H := H) 𝔤 g e) f := by
  let : LieAlgebra ℚ 𝔤 := ratLieAlgebra k 𝔤
  obtain ⟨φ, hφ, h, hh, f, t⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  obtain ⟨g, hg⟩ := exists_basePointsRepresentation_eq_of_mem_intLieAlgebra (H := H) hφ
  refine ⟨g, h, hh, f, ?_⟩
  have hge : Comodule.basePointsRepresentation (H := H) 𝔤 g e = φ • e := by
    rw [← hg]
    rfl
  rwa [hge]

/-- The nonzero nilpotent adjoint orbit attached to a dominant neutral element
`h ∈ b.dominantNeutralElements`: the orbit of `e` for any `sl₂` triple `(h, e, f)`. By openness
of the grade-two centralizer orbit, this does not depend on the choice of `(e, f)`. -/
noncomputable def orbitOfDominantNeutral (h : b.dominantNeutralElements) :
    nonzeroNilpotentOrbits k H := by
  have hex : ∃ e f : 𝔤, IsSl2Triple ((h : 𝔥) : 𝔤) e f :=
    ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  let e := hex.choose
  let f := hex.choose_spec.choose
  have t : IsSl2Triple ((h : 𝔥) : 𝔤) e f := hex.choose_spec.choose_spec
  exact ⟨Comodule.VectorOrbit.mk e,
    mem_nonzeroNilpotentOrbits_mk_iff.mpr ⟨t.isNilpotent_toEnd_e (K := k) (M := 𝔤), t.e_ne_zero⟩⟩

/-- For any `sl₂` triple `(h, e, f)` with dominant neutral element `h`, the orbit attached to `h` is
the adjoint orbit of `e`. -/
theorem orbitOfDominantNeutral_eq_mk {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    (b.orbitOfDominantNeutral h : Comodule.VectorOrbit k H 𝔤) = Comodule.VectorOrbit.mk e := by
  have hex : ∃ e' f' : 𝔤, IsSl2Triple ((h : 𝔥) : 𝔤) e' f' :=
    ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  have t₀ : IsSl2Triple ((h : 𝔥) : 𝔤) hex.choose hex.choose_spec.choose :=
    hex.choose_spec.choose_spec
  obtain ⟨g, -, -, hge, -⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t
  exact Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

/-- **Surjectivity from dominant neutral elements.** Every nonzero nilpotent adjoint orbit arises
from some dominant neutral element `h ∈ b.dominantNeutralElements`. No connectedness hypothesis on
`G` is needed. -/
theorem orbitOfDominantNeutral_surjective :
    Function.Surjective (b.orbitOfDominantNeutral (H := H)) := by
  rintro ⟨O, hO⟩
  induction O using Comodule.VectorOrbit.ind with | h e
  rw [mem_nonzeroNilpotentOrbits_mk_iff] at hO
  obtain ⟨g, h, hh, f, t⟩ :=
    b.exists_basePointsRepresentation_isSl2Triple_mem_dominantNeutralElements hO.1 hO.2
  refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
  rw [b.orbitOfDominantNeutral_eq_mk t, Comodule.VectorOrbit.mk_basePointsRepresentation]

end Surjectivity

end RootPairing.Base

namespace TauCeti

attribute [local instance] Derivation.adjointComodule

section Finiteness

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

variable (k H) in
/-- **Finitely many nonzero nilpotent adjoint orbits.** Over an algebraically closed field of
characteristic zero, if `𝔤` has nondegenerate Killing form, then `G` has only finitely many
nonzero nilpotent adjoint orbits. No connectedness hypothesis on `G` is needed. -/
theorem finite_nonzeroNilpotentOrbits : (nonzeroNilpotentOrbits k H).Finite := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel k 𝔤
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  have : Finite (nonzeroNilpotentOrbits k H) :=
    Finite.of_surjective _ b.orbitOfDominantNeutral_surjective
  exact Set.toFinite _

variable (k H) in
/-- **Finitely many nilpotent adjoint orbits.** Over an algebraically closed field of
characteristic zero, if `𝔤` has nondegenerate Killing form, then `G` has only finitely many
nilpotent adjoint orbits. No connectedness hypothesis on `G` is needed. -/
theorem finite_nilpotentOrbits : (nilpotentOrbits k H).Finite := by
  rw [nilpotentOrbits_eq_insert_zero]
  exact (finite_nonzeroNilpotentOrbits k H).insert _

/-- The number of nonzero nilpotent adjoint orbits is at most the number of dominant neutral
elements for any base `b` of a Cartan subalgebra. -/
theorem ncard_nonzeroNilpotentOrbits_le_dominantNeutralElements
    {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (nonzeroNilpotentOrbits k H).ncard ≤ b.dominantNeutralElements.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_surjective _ b.orbitOfDominantNeutral_surjective

/-- **Upper bound on nonzero nilpotent orbits.** There are at most `3 ^ finrank k 𝔥` nonzero
nilpotent adjoint orbits, where `𝔥` is any Cartan subalgebra of `𝔤`. -/
theorem ncard_nonzeroNilpotentOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nonzeroNilpotentOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  exact (ncard_nonzeroNilpotentOrbits_le_dominantNeutralElements b).trans
    b.ncard_dominantNeutralElements_le

/-- **Upper bound on nilpotent orbits.** There are at most `3 ^ finrank k 𝔥 + 1` nilpotent adjoint
orbits (including the zero orbit), where `𝔥` is any Cartan subalgebra of `𝔤`. -/
theorem ncard_nilpotentOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nilpotentOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 + 1 := by
  rw [nilpotentOrbits_eq_insert_zero]
  exact (Set.ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_nonzeroNilpotentOrbits_le 𝔥) 1)

end Finiteness

end TauCeti

namespace RootPairing.Base

open TauCeti

attribute [local instance] Derivation.adjointComodule

section Classification

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
  (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Conjugate dominant neutral elements are equal (connected `G`).** For a connected finite-type
affine group over an algebraically closed field of characteristic zero, if two dominant neutral
elements in `𝔥` are `G(k)`-conjugate, then they are equal. -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    {h₁ h₂ : 𝔥} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)}
    (hgh : Comodule.basePointsRepresentation (H := H) 𝔤 g (h₁ : 𝔤) = (h₂ : 𝔤)) :
    h₁ = h₂ := by
  refine b.eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq hh₁ hh₂ fun p hp ↦ ?_
  rw [← hgh]
  exact (lift_eval_basePointsRepresentation_eq_of_mem_lieInvariants hp g (h₁ : 𝔤)).symm

/-- **Uniqueness of the dominant neutral element of a nilpotent orbit (connected `G`).** If two
`sl₂` triples have dominant neutral elements in `𝔥` and `G(k)`-conjugate nilpositive elements, then
their neutral elements coincide. -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_e_eq
    {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    {g : WithConv (H →ₐ[k] k)}
    (hge : Comodule.basePointsRepresentation (H := H) 𝔤 g e₁ = e₂) :
    h₁ = h₂ := by
  have : LieAlgebra.HasCentralRadical k 𝔤 :=
    LieAlgebra.hasCentralRadical_of_radical_le k 𝔤 (by rw [LieAlgebra.radical_eq_bot]; exact bot_le)
  have t₁' : IsSl2Triple (Comodule.basePointsRepresentation (H := H) 𝔤 g (h₁ : 𝔤)) e₂
      (Comodule.basePointsRepresentation (H := H) 𝔤 g f₁) := by
    rw [← hge]
    exact t₁.basePointsRepresentation_adjointComodule g
  obtain ⟨u, -, -, huh, -⟩ := t₁'.exists_mem_quotientPointsSubgroup_centralizer_eq t₂
  refine b.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq hh₁ hh₂ (g := u * g) ?_
  simpa only [map_mul, mul_apply_eq_comp] using huh

/-- **Injectivity on dominant neutral elements (connected `G`).** Distinct dominant neutral
elements determine distinct nonzero nilpotent adjoint orbits. -/
theorem orbitOfDominantNeutral_injective :
    Function.Injective (b.orbitOfDominantNeutral (H := H)) := by
  intro h₁ h₂ heq
  have hex₁ : ∃ e₁ f₁ : 𝔤, IsSl2Triple ((h₁ : 𝔥) : 𝔤) e₁ f₁ :=
    ((b.mem_dominantNeutralElements_iff h₁.1).mp h₁.2).1
  have hex₂ : ∃ e₂ f₂ : 𝔤, IsSl2Triple ((h₂ : 𝔥) : 𝔤) e₂ f₂ :=
    ((b.mem_dominantNeutralElements_iff h₂.1).mp h₂.2).1
  have t₁ : IsSl2Triple ((h₁ : 𝔥) : 𝔤) hex₁.choose hex₁.choose_spec.choose :=
    hex₁.choose_spec.choose_spec
  have t₂ : IsSl2Triple ((h₂ : 𝔥) : 𝔤) hex₂.choose hex₂.choose_spec.choose :=
    hex₂.choose_spec.choose_spec
  have hmk : (Comodule.VectorOrbit.mk hex₁.choose : Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk hex₂.choose := by
    have hval := congrArg Subtype.val heq
    rwa [b.orbitOfDominantNeutral_eq_mk t₁, b.orbitOfDominantNeutral_eq_mk t₂] at hval
  obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp hmk
  exact Subtype.ext <|
    b.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_e_eq h₁.2 h₂.2 t₁ t₂ hge

/-- **Bijection with dominant neutral elements (connected `G`).** For a connected finite-type affine
group with semisimple Lie algebra, the nonzero nilpotent adjoint orbits are in bijection with
`b.dominantNeutralElements`. -/
theorem orbitOfDominantNeutral_bijective :
    Function.Bijective (b.orbitOfDominantNeutral (H := H)) :=
  ⟨b.orbitOfDominantNeutral_injective, b.orbitOfDominantNeutral_surjective⟩

/-- The canonical bijection between nonzero nilpotent adjoint orbits of a connected group and the
dominant neutral elements for a base `b`. -/
noncomputable def nonzeroNilpotentOrbitsEquiv :
    nonzeroNilpotentOrbits k H ≃ b.dominantNeutralElements :=
  (Equiv.ofBijective _ b.orbitOfDominantNeutral_bijective).symm

/-- The inverse of `nonzeroNilpotentOrbitsEquiv` is `orbitOfDominantNeutral`. -/
@[simp]
theorem nonzeroNilpotentOrbitsEquiv_symm_apply (h : b.dominantNeutralElements) :
    b.nonzeroNilpotentOrbitsEquiv.symm h = b.orbitOfDominantNeutral h :=
  (rfl)

/-- On the orbit of the nilpositive element of a dominant `sl₂` triple `(h, e, f)`, the equivalence
`nonzeroNilpotentOrbitsEquiv` recovers `h`. -/
theorem nonzeroNilpotentOrbitsEquiv_apply_eq {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    b.nonzeroNilpotentOrbitsEquiv
        ⟨Comodule.VectorOrbit.mk e,
          mem_nonzeroNilpotentOrbits_mk_iff.mpr
            ⟨t.isNilpotent_toEnd_e (K := k) (M := 𝔤), t.e_ne_zero⟩⟩ =
      h := by
  apply b.nonzeroNilpotentOrbitsEquiv.symm.injective
  rw [Equiv.symm_apply_apply, nonzeroNilpotentOrbitsEquiv_symm_apply]
  exact Subtype.ext (b.orbitOfDominantNeutral_eq_mk t).symm

/-- **The weighted Dynkin diagram of a nonzero nilpotent adjoint orbit.** Sends each nonzero
nilpotent orbit of a connected group `G` to the labeling `b.support → Fin 3` attached to its unique
dominant neutral element. -/
noncomputable def orbitWeightedDynkinDiagram :
    nonzeroNilpotentOrbits k H → (b.support → Fin 3) :=
  b.weightedDynkinDiagram ∘ b.nonzeroNilpotentOrbitsEquiv

/-- On the orbit of the nilpositive element of a dominant `sl₂` triple `(h, e, f)`, the orbit
weighted Dynkin diagram equals `b.weightedDynkinDiagram h`. -/
theorem orbitWeightedDynkinDiagram_eq {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    b.orbitWeightedDynkinDiagram
        ⟨Comodule.VectorOrbit.mk e,
          mem_nonzeroNilpotentOrbits_mk_iff.mpr
            ⟨t.isNilpotent_toEnd_e (K := k) (M := 𝔤), t.e_ne_zero⟩⟩ =
      b.weightedDynkinDiagram h := by
  simp [orbitWeightedDynkinDiagram, b.nonzeroNilpotentOrbitsEquiv_apply_eq t]

/-- **Injectivity of the weighted Dynkin diagram on nonzero nilpotent orbits.** Distinct nonzero
nilpotent adjoint orbits of a connected group have distinct weighted Dynkin diagrams. -/
theorem orbitWeightedDynkinDiagram_injective :
    Function.Injective (b.orbitWeightedDynkinDiagram (H := H)) :=
  b.weightedDynkinDiagram_injective.comp b.nonzeroNilpotentOrbitsEquiv.injective

/-- **Classification by weighted Dynkin diagrams.** For two `sl₂` triples with dominant neutral
elements, their nilpositive elements lie in the same `G(k)`-orbit if and only if they have the
same weighted Dynkin diagram. -/
theorem mk_eq_mk_iff_weightedDynkinDiagram_eq {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : 𝔤} (t₁ : IsSl2Triple ((h₁ : 𝔥) : 𝔤) e₁ f₁)
    (t₂ : IsSl2Triple ((h₂ : 𝔥) : 𝔤) e₂ f₂) :
    (Comodule.VectorOrbit.mk e₁ : Comodule.VectorOrbit k H 𝔤) = Comodule.VectorOrbit.mk e₂ ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  constructor
  · intro heq
    have horb : (⟨Comodule.VectorOrbit.mk e₁,
        mem_nonzeroNilpotentOrbits_mk_iff.mpr
          ⟨t₁.isNilpotent_toEnd_e (K := k) (M := 𝔤), t₁.e_ne_zero⟩⟩ :
          nonzeroNilpotentOrbits k H) =
        ⟨Comodule.VectorOrbit.mk e₂,
          mem_nonzeroNilpotentOrbits_mk_iff.mpr
            ⟨t₂.isNilpotent_toEnd_e (K := k) (M := 𝔤), t₂.e_ne_zero⟩⟩ :=
      Subtype.ext heq
    rw [← b.orbitWeightedDynkinDiagram_eq t₁, ← b.orbitWeightedDynkinDiagram_eq t₂, horb]
  · intro hdiag
    obtain rfl := b.weightedDynkinDiagram_injective hdiag
    rw [← b.orbitOfDominantNeutral_eq_mk t₁, ← b.orbitOfDominantNeutral_eq_mk t₂]

/-- **Rational conjugacy criterion.** For two `sl₂` triples with dominant neutral elements in the
Lie algebra of a connected group, their nilpositive elements are `G(k)`-conjugate if and only if
they have the same weighted Dynkin diagram. -/
theorem exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq
    {h₁ h₂ : b.dominantNeutralElements} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple ((h₁ : 𝔥) : 𝔤) e₁ f₁) (t₂ : IsSl2Triple ((h₂ : 𝔥) : 𝔤) e₂ f₂) :
    (∃ g : WithConv (H →ₐ[k] k),
        Comodule.basePointsRepresentation (H := H) 𝔤 g e₁ = e₂) ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  rw [← Comodule.VectorOrbit.mk_eq_mk_iff, b.mk_eq_mk_iff_weightedDynkinDiagram_eq t₁ t₂]

/-- **Exact count of nonzero nilpotent orbits.** For a connected group, the number of nonzero
nilpotent adjoint orbits equals `(b.dominantNeutralElements).ncard`. -/
theorem ncard_nonzeroNilpotentOrbits_eq :
    (nonzeroNilpotentOrbits k H).ncard = b.dominantNeutralElements.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr b.nonzeroNilpotentOrbitsEquiv

/-- **Exact count of nilpotent orbits.** For a connected group, the total number of nilpotent
adjoint orbits (including the zero orbit) equals `(b.dominantNeutralElements).ncard + 1`. -/
theorem ncard_nilpotentOrbits_eq :
    (nilpotentOrbits k H).ncard = b.dominantNeutralElements.ncard + 1 := by
  rw [nilpotentOrbits_eq_insert_zero,
    Set.ncard_insert_of_notMem mk_zero_notMem_nonzeroNilpotentOrbits
      (finite_nonzeroNilpotentOrbits k H),
    b.ncard_nonzeroNilpotentOrbits_eq]

end Classification

end RootPairing.Base
