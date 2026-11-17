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

Let `G = Spec H` be an affine group over a field `k` with finite-dimensional Lie algebra
`𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`. This file defines the sets of nilpotent and
nonzero nilpotent rational adjoint orbits (`TauCeti.nilpotentOrbits`,
`TauCeti.nonzeroNilpotentOrbits`) and proves:

* **Polynomial invariance**: `O(𝔤)^G` (and `S(𝔤*)^𝔤` for connected `G`, char `0`, `IsAlgClosed`)
  is invariant under `G(k)` evaluation (`lift_eval_basePointsRepresentation_eq_of_mem_*`).
* **Scaling cone property**: when `IsKilling k 𝔤`, `e` is `G(k)`-conjugate to `c • e` for `c : kˣ`.
* **Finiteness** (no connectedness): `RootPairing.Base.orbitOfDominantNeutral` surjects from
  `b.dominantNeutralElements` onto `nonzeroNilpotentOrbits k H`, giving
  `finite_nonzeroNilpotentOrbits`, `finite_nilpotentOrbits`, and the `3 ^ rank` bounds.
* **Classification** (connected `G`): `RootPairing.Base.nonzeroNilpotentOrbitsEquiv` is a bijection
  with `b.dominantNeutralElements`, yielding the injective weighted Dynkin diagram map
  `RootPairing.Base.orbitWeightedDynkinDiagram` and exact orbit counts
  (`ncard_nonzeroNilpotentOrbits_eq`, `ncard_nilpotentOrbits_eq`).

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, 1993, Ch. 3.
* B. Kostant, Amer. J. Math. **81** (1959), 973–1032.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Birkhäuser, 2004, §3.
-/

public section

open CategoryTheory LieAlgebra LieAlgebra.IsKilling WithConv
open scoped TensorProduct

namespace TauCeti

open Comodule

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
        (basePointsRepresentation (H := H) 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p := by
  let := Comodule.dual k H 𝔤
  let Φ : SymmetricAlgebra k (Module.Dual k 𝔤) ⊗[k] H →ₐ[k] k :=
    Algebra.TensorProduct.lift (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) g⁻¹.ofConv
      (fun _ _ ↦ Commute.all _ _)
  have heval : SymmetricAlgebra.lift (Module.Dual.eval k 𝔤
        (basePointsRepresentation (H := H) 𝔤 g x)) =
      Φ.comp (symmetricAlgebraCoact k H (Module.Dual k 𝔤)) := by
    refine SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ ?_
    simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply,
      symmetricAlgebraCoact_ι]
    rw [show φ (basePointsRepresentation (H := H) 𝔤 g x) =
        basePointsRepresentation (H := H) (Module.Dual k 𝔤) g⁻¹ φ x by
          rw [basePointsRepresentation_dual_apply, inv_inv],
      basePointsRepresentation_apply, endOfPoint_tmul, one_smul]
    induction Comodule.coact (R := k) (C := H) φ using TensorProduct.inductionOn with
    | tmul ψ h => simp [Φ, Algebra.TensorProduct.lift_tmul, mul_comm]
    | add _ _ hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  have hcoact : symmetricAlgebraCoact k H (Module.Dual k 𝔤) p = p ⊗ₜ[k] (1 : H) := by
    let := adjointPolynomialComoduleAlgebra k H
    have hEq : ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤)) =
        symmetricAlgebraCoact k H (Module.Dual k 𝔤) :=
      SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by
        simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          ComoduleAlgebra.coactAlgHom_apply, adjointPolynomialComoduleAlgebra_coact_ι,
          symmetricAlgebraCoact_ι, dual_coact]
    rw [← hEq, ComoduleAlgebra.coactAlgHom_apply]
    exact mem_adjointInvariantPolynomials.mp hp
  rw [AlgHom.congr_fun heval p, AlgHom.comp_apply, hcoact]
  simp [Φ, Algebra.TensorProduct.lift_tmul]

/-- **Evaluation invariance for Lie-invariant polynomials on a connected group.** For a connected
finite-type affine group over an algebraically closed field of characteristic zero, every
`p ∈ S(𝔤*)^𝔤` takes the same value at `Ad(g) x` and `x`. -/
theorem lift_eval_basePointsRepresentation_eq_of_mem_lieInvariants [CharZero k] [IsAlgClosed k]
    [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤))
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (basePointsRepresentation (H := H) 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p :=
  lift_eval_basePointsRepresentation_eq_of_mem_adjointInvariantPolynomials
    ((adjointInvariantPolynomials_eq_lieInvariants
      (H := FiniteTypeCommHopfAlgCat.of k H)).symm ▸ hp) g x

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
    IsNilpotent (ad R 𝔤 (basePointsRepresentation (H := H) 𝔤 g x)) ↔ IsNilpotent (ad R 𝔤 x) := by
  let φ := Derivation.basePointsAdjointLieEquiv (R := R) (H := H) g
  have hpow : ∀ n y, (ad R 𝔤 (basePointsRepresentation (H := H) 𝔤 g x) ^ n) y =
      φ ((ad R 𝔤 x ^ n) (φ.symm y)) := fun n ↦ by
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp, ih, ad_apply, ad_apply,
        ← Derivation.basePointsAdjointLieEquiv_apply, ← LieEquiv.map_lie]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, LinearMap.ext fun y ↦ φ.injective ?_⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, LinearMap.ext fun y ↦ by rw [hpow, hn, LinearMap.zero_apply, map_zero]; rfl⟩⟩
  have hy := LinearMap.congr_fun hn (φ y)
  rw [hpow, LieEquiv.symm_apply_apply, LinearMap.zero_apply] at hy
  exact hy.trans (map_zero φ).symm

end AdjointInvariance

section Definitions

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The set of **nilpotent adjoint orbits** of `G = Spec H`. -/
noncomputable def nilpotentOrbits : Set (VectorOrbit k H 𝔤) :=
  VectorOrbit.mk '' {x : 𝔤 | IsNilpotent (ad k 𝔤 x)}

/-- The set of **nonzero nilpotent adjoint orbits** of `G = Spec H`. -/
noncomputable def nonzeroNilpotentOrbits : Set (VectorOrbit k H 𝔤) :=
  {O ∈ nilpotentOrbits k H | O ≠ VectorOrbit.mk (0 : 𝔤)}

variable {k H}

/-- The orbit of `x` is nilpotent if and only if `ad x` is nilpotent. -/
@[simp]
theorem mem_nilpotentOrbits_mk_iff {x : 𝔤} :
    (VectorOrbit.mk x : VectorOrbit k H 𝔤) ∈ nilpotentOrbits k H ↔ IsNilpotent (ad k 𝔤 x) :=
  ⟨fun ⟨y, hy, hyx⟩ ↦ let ⟨g, hg⟩ := VectorOrbit.mk_eq_mk_iff.mp hyx
      hg ▸ (isNilpotent_ad_basePointsRepresentation_iff g y).mpr hy,
    fun hx ↦ ⟨x, hx, rfl⟩⟩

/-- The orbit of `x` is a nonzero nilpotent orbit iff `ad x` is nilpotent and `x ≠ 0`. -/
@[simp]
theorem mem_nonzeroNilpotentOrbits_mk_iff {x : 𝔤} :
    (VectorOrbit.mk x : VectorOrbit k H 𝔤) ∈ nonzeroNilpotentOrbits k H ↔
      IsNilpotent (ad k 𝔤 x) ∧ x ≠ 0 := by simp [nonzeroNilpotentOrbits]

/-- The zero orbit is nilpotent. -/
theorem mk_zero_mem_nilpotentOrbits :
    (VectorOrbit.mk (0 : 𝔤) : VectorOrbit k H 𝔤) ∈ nilpotentOrbits k H :=
  mem_nilpotentOrbits_mk_iff.mpr (by rw [map_zero]; exact IsNilpotent.zero)

/-- The zero orbit is not a nonzero nilpotent orbit. -/
theorem mk_zero_notMem_nonzeroNilpotentOrbits :
    (VectorOrbit.mk (0 : 𝔤) : VectorOrbit k H 𝔤) ∉ nonzeroNilpotentOrbits k H := by
  simp [nonzeroNilpotentOrbits]

/-- Nonzero nilpotent orbits are nilpotent orbits. -/
theorem nonzeroNilpotentOrbits_subset_nilpotentOrbits :
    nonzeroNilpotentOrbits k H ⊆ nilpotentOrbits k H := fun _ h ↦ h.1

/-- The set of nilpotent orbits is obtained by inserting the zero orbit into the nonzero ones. -/
theorem nilpotentOrbits_eq_insert_zero :
    nilpotentOrbits k H = insert (VectorOrbit.mk (0 : 𝔤)) (nonzeroNilpotentOrbits k H) := by
  ext O; by_cases h : O = VectorOrbit.mk (0 : 𝔤) <;> simp [nonzeroNilpotentOrbits, h]

/-- In a trivial (rank-zero) Lie algebra, the only nilpotent orbit is the zero orbit. -/
theorem nilpotentOrbits_eq_singleton_of_subsingleton [Subsingleton 𝔤] :
    nilpotentOrbits k H = {VectorOrbit.mk (0 : 𝔤)} := by
  ext O; induction O using VectorOrbit.ind with | h x; simp [Subsingleton.elim x 0]

/-- A trivial (rank-zero) Lie algebra has no nonzero nilpotent orbits. -/
theorem nonzeroNilpotentOrbits_eq_empty_of_subsingleton [Subsingleton 𝔤] :
    nonzeroNilpotentOrbits k H = ∅ := by
  ext O; induction O using VectorOrbit.ind with | h x; simp [Subsingleton.elim x 0]

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

/-- **Scaling invariance of nilpotent elements.** When `IsKilling k 𝔤`, every `ad`-nilpotent `e`
is `G(k)`-conjugate to `c • e` for every unit `c : kˣ` (no connectedness needed). -/
theorem exists_basePointsRepresentation_smul_eq_of_isNilpotent_ad [IsKilling k 𝔤]
    {e : 𝔤} (he : IsNilpotent (ad k 𝔤 e)) (c : kˣ) :
    ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) 𝔤 g e = (c : k) • e := by
  by_cases he0 : e = 0
  · exact ⟨1, by simp [he0]⟩
  · obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
    obtain ⟨g, -, -, hge, -⟩ :=
      t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq
        (t.rescale c)
    exact ⟨g, hge⟩

/-- **Nilpotent orbits are cones.** Rescaling `e` by `c : kˣ` preserves its adjoint orbit. -/
theorem mk_smul_eq_of_isNilpotent_ad [IsKilling k 𝔤] {e : 𝔤}
    (he : IsNilpotent (ad k 𝔤 e)) (c : kˣ) :
    (VectorOrbit.mk ((c : k) • e) : VectorOrbit k H 𝔤) = VectorOrbit.mk e :=
  (VectorOrbit.mk_eq_mk_iff.mpr
    (exists_basePointsRepresentation_smul_eq_of_isNilpotent_ad he c)).symm

end Scaling

end TauCeti

/-! ### Dominant neutral elements, finiteness, and weighted Dynkin diagram classification -/

namespace RootPairing.Base

open TauCeti Comodule

universe u

attribute [local instance] Derivation.adjointComodule

section Surjectivity

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
  (b : (rootSystem 𝔥).Base)

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- Every nonzero `ad`-nilpotent element is `G(k)`-conjugate to the nilpositive element of an `sl₂`
triple with neutral element dominant for `b` (no connectedness needed). -/
theorem exists_basePointsRepresentation_isSl2Triple_mem_dominantNeutralElements
    {e : 𝔤} (he : IsNilpotent (ad k 𝔤 e)) (he0 : e ≠ 0) :
    ∃ g : WithConv (H →ₐ[k] k), ∃ h ∈ b.dominantNeutralElements, ∃ f : 𝔤,
      IsSl2Triple (h : 𝔤) (basePointsRepresentation (H := H) 𝔤 g e) f := by
  let : LieAlgebra ℚ 𝔤 := ratLieAlgebra k 𝔤
  obtain ⟨φ, hφ, h, hh, f, t⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  obtain ⟨g, hg⟩ := exists_basePointsRepresentation_eq_of_mem_intLieAlgebra (H := H) hφ
  exact ⟨g, h, hh, f, by
    rwa [show basePointsRepresentation (H := H) 𝔤 g e = φ • e by rw [← hg]; rfl]⟩

/-- The nonzero nilpotent adjoint orbit attached to a dominant neutral element `h`. -/
noncomputable def orbitOfDominantNeutral (h : b.dominantNeutralElements) :
    nonzeroNilpotentOrbits k H :=
  have hex : ∃ e f : 𝔤, IsSl2Triple ((h : 𝔥) : 𝔤) e f :=
    ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  ⟨VectorOrbit.mk hex.choose, mem_nonzeroNilpotentOrbits_mk_iff.mpr
    ⟨hex.choose_spec.choose_spec.isNilpotent_toEnd_e (K := k) (M := 𝔤),
      hex.choose_spec.choose_spec.e_ne_zero⟩⟩

/-- For any `sl₂` triple `(h, e, f)` with dominant `h`, `orbitOfDominantNeutral h` is `mk e`. -/
theorem orbitOfDominantNeutral_eq_mk {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    (b.orbitOfDominantNeutral h : VectorOrbit k H 𝔤) = VectorOrbit.mk e := by
  have hex : ∃ e' f' : 𝔤, IsSl2Triple ((h : 𝔥) : 𝔤) e' f' :=
    ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  obtain ⟨g, -, -, hge, -⟩ := hex.choose_spec.choose_spec
    |>.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t
  exact VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

/-- **Surjectivity from dominant neutral elements** (no connectedness hypothesis needed). -/
theorem orbitOfDominantNeutral_surjective :
    Function.Surjective (b.orbitOfDominantNeutral (H := H)) := by
  rintro ⟨O, hO⟩
  induction O using VectorOrbit.ind with | h e
  rw [mem_nonzeroNilpotentOrbits_mk_iff] at hO
  obtain ⟨g, h, hh, f, t⟩ :=
    b.exists_basePointsRepresentation_isSl2Triple_mem_dominantNeutralElements hO.1 hO.2
  exact ⟨⟨h, hh⟩, Subtype.ext <| by
    rw [b.orbitOfDominantNeutral_eq_mk t, VectorOrbit.mk_basePointsRepresentation]⟩

end Surjectivity

end RootPairing.Base

namespace TauCeti

open Comodule

attribute [local instance] Derivation.adjointComodule

section Finiteness

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

variable (k H) in
/-- **Finitely many nonzero nilpotent adjoint orbits** (no connectedness hypothesis needed). -/
theorem finite_nonzeroNilpotentOrbits : (nonzeroNilpotentOrbits k H).Finite := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel k 𝔤
  let b := (rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  have : Finite (nonzeroNilpotentOrbits k H) :=
    Finite.of_surjective _ b.orbitOfDominantNeutral_surjective
  exact Set.toFinite _

variable (k H) in
/-- **Finitely many nilpotent adjoint orbits** (no connectedness hypothesis needed). -/
theorem finite_nilpotentOrbits : (nilpotentOrbits k H).Finite :=
  nilpotentOrbits_eq_insert_zero (k := k) (H := H) ▸ (finite_nonzeroNilpotentOrbits k H).insert _

/-- The number of nonzero nilpotent adjoint orbits is at most `b.dominantNeutralElements.ncard`. -/
theorem ncard_nonzeroNilpotentOrbits_le_dominantNeutralElements
    {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra] (b : (rootSystem 𝔥).Base) :
    (nonzeroNilpotentOrbits k H).ncard ≤ b.dominantNeutralElements.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_surjective _ b.orbitOfDominantNeutral_surjective

/-- **Upper bound on nonzero nilpotent orbits**: at most `3 ^ finrank k 𝔥`. -/
theorem ncard_nonzeroNilpotentOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nonzeroNilpotentOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 :=
  let b := (rootSystem 𝔥).nonempty_base.some
  (ncard_nonzeroNilpotentOrbits_le_dominantNeutralElements b).trans
    b.ncard_dominantNeutralElements_le

/-- **Upper bound on nilpotent orbits**: at most `3 ^ finrank k 𝔥 + 1`. -/
theorem ncard_nilpotentOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nilpotentOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 + 1 := by
  rw [nilpotentOrbits_eq_insert_zero]
  exact (Set.ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_nonzeroNilpotentOrbits_le 𝔥) 1)

end Finiteness

end TauCeti

namespace RootPairing.Base

open TauCeti Comodule

attribute [local instance] Derivation.adjointComodule

section Classification

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
  (b : (rootSystem 𝔥).Base)

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Conjugate dominant neutral elements are equal (connected `G`).** -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    {h₁ h₂ : 𝔥} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)} (hgh : basePointsRepresentation (H := H) 𝔤 g (h₁ : 𝔤) = (h₂ : 𝔤)) :
    h₁ = h₂ :=
  b.eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq hh₁ hh₂ fun _ hp ↦
    hgh ▸ (lift_eval_basePointsRepresentation_eq_of_mem_lieInvariants hp g (h₁ : 𝔤)).symm

/-- **Uniqueness of the dominant neutral element of a nilpotent orbit (connected `G`).** -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_e_eq
    {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    {g : WithConv (H →ₐ[k] k)} (hge : basePointsRepresentation (H := H) 𝔤 g e₁ = e₂) :
    h₁ = h₂ := by
  have : HasCentralRadical k 𝔤 :=
    hasCentralRadical_of_radical_le k 𝔤 (by rw [radical_eq_bot]; exact bot_le)
  have t₁' : IsSl2Triple (basePointsRepresentation (H := H) 𝔤 g (h₁ : 𝔤)) e₂
      (basePointsRepresentation (H := H) 𝔤 g f₁) :=
    hge ▸ t₁.basePointsRepresentation_adjointComodule g
  obtain ⟨u, -, -, huh, -⟩ := t₁'.exists_mem_quotientPointsSubgroup_centralizer_eq t₂
  exact b.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq hh₁ hh₂ (g := u * g)
    (by simpa only [map_mul, mul_apply_eq_comp] using huh)

/-- **Injectivity on dominant neutral elements (connected `G`).** -/
theorem orbitOfDominantNeutral_injective :
    Function.Injective (b.orbitOfDominantNeutral (H := H)) := by
  intro h₁ h₂ heq
  have hex₁ := ((b.mem_dominantNeutralElements_iff h₁.1).mp h₁.2).1
  have hex₂ := ((b.mem_dominantNeutralElements_iff h₂.1).mp h₂.2).1
  have hmk : (VectorOrbit.mk hex₁.choose : VectorOrbit k H 𝔤) = VectorOrbit.mk hex₂.choose := by
    have hval := congrArg Subtype.val heq
    rwa [b.orbitOfDominantNeutral_eq_mk hex₁.choose_spec.choose_spec,
      b.orbitOfDominantNeutral_eq_mk hex₂.choose_spec.choose_spec] at hval
  obtain ⟨g, hge⟩ := VectorOrbit.mk_eq_mk_iff.mp hmk
  exact Subtype.ext <| b.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_e_eq
    h₁.2 h₂.2 hex₁.choose_spec.choose_spec hex₂.choose_spec.choose_spec hge

/-- **Bijection with dominant neutral elements (connected `G`).** -/
theorem orbitOfDominantNeutral_bijective :
    Function.Bijective (b.orbitOfDominantNeutral (H := H)) :=
  ⟨b.orbitOfDominantNeutral_injective, b.orbitOfDominantNeutral_surjective⟩

/-- Canonical bijection between nonzero nilpotent orbits of a connected group and
`b.dominantNeutralElements`. -/
noncomputable def nonzeroNilpotentOrbitsEquiv :
    nonzeroNilpotentOrbits k H ≃ b.dominantNeutralElements :=
  (Equiv.ofBijective _ b.orbitOfDominantNeutral_bijective).symm

/-- The inverse of `nonzeroNilpotentOrbitsEquiv` is `orbitOfDominantNeutral`. -/
@[simp]
theorem nonzeroNilpotentOrbitsEquiv_symm_apply (h : b.dominantNeutralElements) :
    b.nonzeroNilpotentOrbitsEquiv.symm h = b.orbitOfDominantNeutral h := (rfl)

/-- On the orbit of `e` in a dominant `sl₂` triple `(h, e, f)`, `nonzeroNilpotentOrbitsEquiv`
recovers `h`. -/
theorem nonzeroNilpotentOrbitsEquiv_apply_eq {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    b.nonzeroNilpotentOrbitsEquiv ⟨VectorOrbit.mk e,
        mem_nonzeroNilpotentOrbits_mk_iff.mpr
          ⟨t.isNilpotent_toEnd_e (K := k) (M := 𝔤), t.e_ne_zero⟩⟩ = h :=
  b.nonzeroNilpotentOrbitsEquiv.symm.injective <| by
    rw [Equiv.symm_apply_apply, nonzeroNilpotentOrbitsEquiv_symm_apply]
    exact Subtype.ext (b.orbitOfDominantNeutral_eq_mk t).symm

/-- **The weighted Dynkin diagram of a nonzero nilpotent adjoint orbit** for a connected group. -/
noncomputable def orbitWeightedDynkinDiagram :
    nonzeroNilpotentOrbits k H → (b.support → Fin 3) :=
  b.weightedDynkinDiagram ∘ b.nonzeroNilpotentOrbitsEquiv

/-- On the orbit of `e` in a dominant `sl₂` triple `(h, e, f)`, `orbitWeightedDynkinDiagram`
equals `b.weightedDynkinDiagram h`. -/
theorem orbitWeightedDynkinDiagram_eq {h : b.dominantNeutralElements} {e f : 𝔤}
    (t : IsSl2Triple ((h : 𝔥) : 𝔤) e f) :
    b.orbitWeightedDynkinDiagram ⟨VectorOrbit.mk e,
        mem_nonzeroNilpotentOrbits_mk_iff.mpr
          ⟨t.isNilpotent_toEnd_e (K := k) (M := 𝔤), t.e_ne_zero⟩⟩ = b.weightedDynkinDiagram h := by
  simp [orbitWeightedDynkinDiagram, b.nonzeroNilpotentOrbitsEquiv_apply_eq t]

/-- **Injectivity of the weighted Dynkin diagram on nonzero nilpotent orbits.** -/
theorem orbitWeightedDynkinDiagram_injective :
    Function.Injective (b.orbitWeightedDynkinDiagram (H := H)) :=
  b.weightedDynkinDiagram_injective.comp b.nonzeroNilpotentOrbitsEquiv.injective

/-- **Classification by weighted Dynkin diagrams.** Two dominant `sl₂` triples have nilpositive
elements in the same `G(k)`-orbit iff they have the same weighted Dynkin diagram. -/
theorem mk_eq_mk_iff_weightedDynkinDiagram_eq {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : 𝔤} (t₁ : IsSl2Triple ((h₁ : 𝔥) : 𝔤) e₁ f₁)
    (t₂ : IsSl2Triple ((h₂ : 𝔥) : 𝔤) e₂ f₂) :
    (VectorOrbit.mk e₁ : VectorOrbit k H 𝔤) = VectorOrbit.mk e₂ ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  refine ⟨fun heq ↦ ?_, fun hdiag ↦ ?_⟩
  · rw [← b.orbitWeightedDynkinDiagram_eq t₁, ← b.orbitWeightedDynkinDiagram_eq t₂]
    exact congrArg (b.orbitWeightedDynkinDiagram (H := H)) (Subtype.ext heq)
  · obtain rfl := b.weightedDynkinDiagram_injective hdiag
    rw [← b.orbitOfDominantNeutral_eq_mk t₁, ← b.orbitOfDominantNeutral_eq_mk t₂]

/-- **Rational conjugacy criterion.** Two dominant `sl₂` triples have `G(k)`-conjugate nilpositive
elements iff they have the same weighted Dynkin diagram. -/
theorem exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq
    {h₁ h₂ : b.dominantNeutralElements} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple ((h₁ : 𝔥) : 𝔤) e₁ f₁) (t₂ : IsSl2Triple ((h₂ : 𝔥) : 𝔤) e₂ f₂) :
    (∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) 𝔤 g e₁ = e₂) ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  rw [← VectorOrbit.mk_eq_mk_iff, b.mk_eq_mk_iff_weightedDynkinDiagram_eq t₁ t₂]

/-- **Exact count of nonzero nilpotent orbits** for a connected group. -/
theorem ncard_nonzeroNilpotentOrbits_eq :
    (nonzeroNilpotentOrbits k H).ncard = b.dominantNeutralElements.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr b.nonzeroNilpotentOrbitsEquiv

/-- **Exact count of nilpotent orbits** for a connected group. -/
theorem ncard_nilpotentOrbits_eq :
    (nilpotentOrbits k H).ncard = b.dominantNeutralElements.ncard + 1 := by
  rw [nilpotentOrbits_eq_insert_zero, Set.ncard_insert_of_notMem
    mk_zero_notMem_nonzeroNilpotentOrbits (finite_nonzeroNilpotentOrbits k H),
    b.ncard_nonzeroNilpotentOrbits_eq]

end Classification

end RootPairing.Base
