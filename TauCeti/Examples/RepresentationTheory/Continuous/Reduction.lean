/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.RepresentationTheory.Continuous.IntegralModel.Reduction
public import TauCeti.RepresentationTheory.Continuous.Reduction
public import TauCeti.Topology.Algebra.Ring.Compact
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Examples for the raw reduction of a continuous representation

Give the residue field `𝔽_ℓ = ℤ_ℓ ⧸ ℓ` of `ℤ_ℓ` the discrete topology; the residue map is
continuous because the maximal ideal of `ℤ_ℓ` is open (`IsLocalRing.continuous_residue`). Let
`ℤ` (discrete) act on `ℚ_ℓ²` through the unipotent matrix `(1 a; 0 1)` with `a ∈ ℤ_ℓ^×`. The
stable lattice `ℤ_ℓ²` has the action `n ↦ (1 na; 0 1)` in its standard basis, and the stable
lattice `ℤ_ℓ e₁ ⊕ ℓℤ_ℓ e₂` has the action `n ↦ (1 ℓna; 0 1)` in its basis `e₁, ℓ e₂`. The
inclusion of the second lattice in the first, `diag(1, ℓ)` in these bases, becomes an isomorphism
after extending scalars to `ℚ_ℓ`, so both are lattices of the same `ℚ_ℓ`-representation. Their
raw reductions are not isomorphic: the first is a non-trivial unipotent representation of `ℤ` on
`𝔽_ℓ²`, the second is trivial. So the raw reduction depends on the lattice, and no
semisimplification is applied. In particular the two lattices are not isomorphic over `ℤ_ℓ`
(`isEmpty_iso_unipotent`).

For a field `K` in which `ℓ` is invertible, any integral model of the line `ℚ_ℓ(1)` of the
`ℓ`-adic cyclotomic character of `G_K` reduces to the mod `ℓ` cyclotomic character: `g` acts on
the reduction by the residue of a natural number `a` with `g ζ = ζ ^ a` for every `ℓ`-th root of
unity `ζ` (`exists_reduction_qlOne`).
-/

public section

noncomputable section

open IsLocalRing TensorProduct

namespace TauCeti.ContinuousRep.ReductionCheck

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The residue field of `ℤ_ℓ` with the discrete topology. -/
local instance : TopologicalSpace (ResidueField ℤ_[ℓ]) := ⊥

local instance : DiscreteTopology (ResidueField ℤ_[ℓ]) := ⟨rfl⟩

local instance : ContinuousSMul ℤ_[ℓ] (ResidueField ℤ_[ℓ]) :=
  continuousSMul_of_algebraMap _ _ (by
    simpa only [ResidueField.algebraMap_eq] using continuous_residue (isOpen_maximalIdeal ℤ_[ℓ]))

/-- The module topology on the reduction `𝔽_ℓ ⊗ M` of a `ℤ_ℓ`-module. -/
local instance (M : Type*) [AddCommGroup M] [Module ℤ_[ℓ] M] :
    TopologicalSpace (ResidueField ℤ_[ℓ] ⊗[ℤ_[ℓ]] M) :=
  moduleTopology (ResidueField ℤ_[ℓ]) _

local instance (M : Type*) [AddCommGroup M] [Module ℤ_[ℓ] M] :
    IsModuleTopology (ResidueField ℤ_[ℓ]) (ResidueField ℤ_[ℓ] ⊗[ℤ_[ℓ]] M) :=
  ⟨rfl⟩

/-- The module topology on `ℚ_ℓ ⊗ ℤ_ℓ²`. -/
local instance : TopologicalSpace (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])) :=
  moduleTopology ℚ_[ℓ] _

local instance : IsModuleTopology ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])) :=
  ⟨rfl⟩

/-- The representation `n ↦ (1 nb; 0 1)` of `ℤ`, written multiplicatively, on `ℤ_ℓ²`. -/
def unipotentRep (b : ℤ_[ℓ]) : Representation ℤ_[ℓ] (Multiplicative ℤ) (Fin 2 → ℤ_[ℓ]) where
  toFun n := (!![1, (n.toAdd : ℤ_[ℓ]) * b; 0, 1]).mulVecLin
  map_one' := by simp [← Matrix.one_fin_two, Module.End.one_eq_id]
  map_mul' m n := by
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, Matrix.mul_fin_two]
    simp [add_mul, add_comm]

/-- The continuous representation `n ↦ (1 nb; 0 1)` of the discrete group `ℤ` on `ℤ_ℓ²`. -/
def unipotent (b : ℤ_[ℓ]) : ContinuousRep (Multiplicative ℤ) ℤ_[ℓ] (Fin 2 → ℤ_[ℓ]) where
  toRepresentation := unipotentRep ℓ b
  continuous_action := continuous_prod_of_discrete_left.2 fun g ↦
    IsModuleTopology.continuous_of_linearMap (R := ℤ_[ℓ]) (unipotentRep ℓ b g)

theorem unipotent_apply (b : ℤ_[ℓ]) (n : Multiplicative ℤ) (v : Fin 2 → ℤ_[ℓ]) :
    unipotent ℓ b n v = ![v 0 + (n.toAdd : ℤ_[ℓ]) * b * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [unipotent, unipotentRep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The two lattices span the same `ℚ_ℓ`-representation**: the inclusion of
`ℤ_ℓ e₁ ⊕ ℓℤ_ℓ e₂` in `ℤ_ℓ²`, which is `diag(1, ℓ)` from the basis `e₁, ℓ e₂` to `e₁, e₂`,
intertwines `unipotent (ℓ * b)` with `unipotent b` and becomes an isomorphism over `ℚ_ℓ`. -/
theorem nonempty_iso_baseChange_unipotent (b : ℤ_[ℓ]) :
    Nonempty (Iso ((unipotent ℓ (ℓ * b)).baseChange ℚ_[ℓ]) ((unipotent ℓ b).baseChange ℚ_[ℓ])) := by
  -- `diag(1, ℓ)` and `diag(ℓ, 1)` intertwine the two actions and compose to `ℓ` either way.
  let f : (unipotent ℓ (ℓ * b)).toRepresentation.IntertwiningMap
      (unipotent ℓ b).toRepresentation :=
    ⟨(Matrix.diagonal ![1, (ℓ : ℤ_[ℓ])]).mulVecLin, fun n ↦ LinearMap.ext fun v ↦ by
      ext i; fin_cases i <;>
        simp [unipotent_apply, Matrix.mulVec_diagonal, mul_add, mul_assoc, mul_left_comm]⟩
  let g : (unipotent ℓ b).toRepresentation.IntertwiningMap
      (unipotent ℓ (ℓ * b)).toRepresentation :=
    ⟨(Matrix.diagonal ![(ℓ : ℤ_[ℓ]), 1]).mulVecLin, fun n ↦ LinearMap.ext fun v ↦ by
      ext i; fin_cases i <;>
        simp [unipotent_apply, Matrix.mulVec_diagonal, mul_add, mul_assoc, mul_left_comm]⟩
  have hgf (v : Fin 2 → ℤ_[ℓ]) : g (f v) = (ℓ : ℤ_[ℓ]) • v := by
    ext i; fin_cases i <;> simp [f, g, Matrix.mulVec_diagonal]
  have hfg (v : Fin 2 → ℤ_[ℓ]) : f (g v) = (ℓ : ℤ_[ℓ]) • v := by
    ext i; fin_cases i <;> simp [f, g, Matrix.mulVec_diagonal]
  have hℓ : IsUnit (algebraMap ℤ_[ℓ] ℚ_[ℓ] ℓ) := by
    simpa using (Fact.out : ℓ.Prime).ne_zero
  have e := (f.baseChange ℚ_[ℓ]).ofBijective
    (Representation.IntertwiningMap.baseChange_bijective_of_comp_eq_smul hgf hfg _ hℓ hℓ)
  rw [← toRepresentation_baseChange, ← toRepresentation_baseChange] at e
  exact ⟨.ofEquiv e⟩

/-- The identification `𝔽_ℓ ⊗ ℤ_ℓ² ≅ 𝔽_ℓ²`. -/
noncomputable abbrev coords : ResidueField ℤ_[ℓ] ⊗[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ]) ≃ₗ[ResidueField ℤ_[ℓ]]
    (Fin 2 → ResidueField ℤ_[ℓ]) :=
  piScalarRight ℤ_[ℓ] (ResidueField ℤ_[ℓ]) (ResidueField ℤ_[ℓ]) (Fin 2)

/-- In coordinates, the reduction of `unipotent b` acts by `(1 n·b; 0 1)` with `b`
reduced modulo `ℓ`. -/
theorem coords_reduction_unipotent (b : ℤ_[ℓ]) (n : Multiplicative ℤ)
    (x : ResidueField ℤ_[ℓ] ⊗[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])) :
    coords ℓ ((unipotent ℓ b).reduction n x) =
      ![coords ℓ x 0 + (n.toAdd : ResidueField ℤ_[ℓ]) * residue ℤ_[ℓ] b * coords ℓ x 1,
        coords ℓ x 1] := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    ext i
    fin_cases i <;> simp [reduction, baseChange_apply, unipotent_apply, Algebra.smul_def,
      ResidueField.algebraMap_eq, mul_add, mul_comm, mul_left_comm]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i
    fin_cases i <;> simp [mul_add, add_add_add_comm]

/-- **The lattice `ℤ_ℓ²` reduces to a non-trivial representation**: for a unit `a`, the
generator of `ℤ` does not act trivially on the reduction of `(1 a; 0 1)`. -/
theorem reduction_unipotent_ne_one {a : ℤ_[ℓ]} (ha : IsUnit a) :
    (unipotent ℓ a).reduction (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  have h' := congr_arg (fun f ↦ coords ℓ (f ((coords ℓ).symm ![0, 1])) 0) h
  simp only [coords_reduction_unipotent, LinearEquiv.apply_symm_apply, one_apply_eq_self] at h'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, toAdd_ofAdd,
    Int.cast_one, one_mul, mul_one, zero_add] at h'
  exact (ha.map (residue ℤ_[ℓ])).ne_zero h'

/-- **The lattice `ℤ_ℓ e₁ ⊕ ℓℤ_ℓ e₂` reduces to the trivial representation**: in the basis
`e₁, ℓ e₂` the action is `(1 ℓa; 0 1)`, and `ℓ` vanishes in `𝔽_ℓ`. -/
theorem reduction_unipotent_ell_mul_eq_one (a : ℤ_[ℓ]) (n : Multiplicative ℤ) :
    (unipotent ℓ (ℓ * a)).reduction n = 1 := by
  refine LinearMap.ext fun x ↦ (coords ℓ).injective ?_
  have hℓ : residue ℤ_[ℓ] ((ℓ : ℤ_[ℓ]) * a) = 0 := by
    rw [residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ (by simp [PadicInt.maximalIdeal_eq_span_p])
  rw [coords_reduction_unipotent, hℓ]
  ext i
  fin_cases i <;> simp

/-- The raw reductions of the two lattices are not isomorphic, although the lattices span
isomorphic `ℚ_ℓ`-representations (`nonempty_iso_baseChange_unipotent`). -/
theorem isEmpty_iso_reduction {a : ℤ_[ℓ]} (ha : IsUnit a) :
    IsEmpty (Iso (unipotent ℓ a).reduction (unipotent ℓ (ℓ * a)).reduction) := by
  refine ⟨fun e ↦ reduction_unipotent_ne_one ℓ ha (LinearMap.ext fun x ↦ EquivLike.injective e ?_)⟩
  rw [e.isIntertwining, reduction_unipotent_ell_mul_eq_one, one_apply_eq_self, one_apply_eq_self]

/-- **The two lattices are not isomorphic over `ℤ_ℓ`**, although they become isomorphic over `ℚ_ℓ`
(`nonempty_iso_baseChange_unipotent`): an isomorphism would reduce to an isomorphism of the raw
reductions, which `isEmpty_iso_reduction` excludes. So isomorphism over `ℤ_ℓ` is not conjugacy
over the fraction field. -/
theorem isEmpty_iso_unipotent {a : ℤ_[ℓ]} (ha : IsUnit a) :
    IsEmpty (Iso (unipotent ℓ a) (unipotent ℓ (ℓ * a))) :=
  ⟨fun e ↦ (isEmpty_iso_reduction ℓ ha).false (e.baseChange (ResidueField ℤ_[ℓ]))⟩

/-! ### Models of `ℚ_ℓ(1)` -/

section Cyclotomic

variable (K : Type*) [Field K] [NeZero (ℓ : K)]

/-- The line `ℚ_ℓ(1)`: the absolute Galois group of `K` acting on `ℚ_ℓ` through the `ℓ`-adic
cyclotomic character. -/
abbrev qlOne : ContinuousRep (Field.absoluteGaloisGroup K) ℚ_[ℓ] ℚ_[ℓ] :=
  ofCharacter (unitsMapCharacter ℚ_[ℓ] (continuousLocalCyclotomicCharacter ℓ K))

/-- **Any model of `ℚ_ℓ(1)` reduces to the mod `ℓ` cyclotomic character.** For an integral model
`Λ` of `ℚ_ℓ(1)` (with its `ℤ_ℓ`-module topology) and `g ∈ G_K`, there is a natural number `a`
with `g ζ = ζ ^ a` for every `ℓ`-th root of unity `ζ` in `K^alg`, and `g` acts on the reduction
of `Λ` by `a mod ℓ`. -/
theorem exists_reduction_qlOne (Λ : GaloisLattice.IntegralModel ℤ_[ℓ] (qlOne ℓ K))
    [IsModuleTopology ℤ_[ℓ] Λ.lattice] (g : Field.absoluteGaloisGroup K) :
    ∃ a : ℕ, (∀ ζ : AlgebraicClosure K, ζ ^ ℓ = 1 → g.toRingEquiv ζ = ζ ^ a) ∧
      ∀ y, Λ.toContinuousRep.reduction g y = (a : ResidueField ℤ_[ℓ]) • y := by
  set u : ℤ_[ℓ] := (localCyclotomicCharacter ℓ K g : ℤ_[ℓ])
  refine ⟨u.appr 1, fun ζ hζ ↦ ?_, fun y ↦ ?_⟩
  · have (i : ℕ) : HasEnoughRootsOfUnity (AlgebraicClosure K) (ℓ ^ i) :=
      AlgebraicClosure.hasEnoughRootsOfUnity_pow K ℓ i
    simpa only [u, localCyclotomicCharacter_apply, PadicInt.val_toZModPow_eq_appr] using
      cyclotomicCharacter.spec ℓ (n := 1) g.toRingEquiv ζ (by rwa [pow_one])
  · rw [Λ.reduction_toContinuousRep_ofCharacter_apply (c := u) (by simp [u]),
      ← map_natCast (residue ℤ_[ℓ])]
    congr 1
    exact Ideal.Quotient.eq.2 <| by
      simpa [PadicInt.maximalIdeal_eq_span_p] using PadicInt.appr_spec 1 u

end Cyclotomic

end TauCeti.ContinuousRep.ReductionCheck

end
