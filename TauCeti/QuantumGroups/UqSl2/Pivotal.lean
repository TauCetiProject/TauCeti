/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Trace
public import TauCeti.QuantumGroups.UqSl2.Antipode
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic

/-!
# The spherical category of finite-dimensional `U_q(sl₂)`-modules

The element `K⁻¹` of `U_q(sl₂)` is group-like, and the square of the antipode is conjugation by
it, `S²(x) = K⁻¹ x K`. The generic constructions for finite-dimensional modules over a Hopf
algebra therefore apply with `g = K⁻¹`:

* `UqSl2.rigidCategory q`: the rigid structure on `FiniteHopfModuleCat ℂ (UqSl2 q)`, with right
  duals the contragredients through the antipode `S` and left duals the contragredients through
  `S⁻¹`;
* `UqSl2.pivotalCategory q`: the pivotal structure `j_V(v)(φ) = φ(K⁻¹ v)`.

The pivotal traces of an endomorphism `f` of `V` are `rightTrace f = tr_V(K⁻¹ f)` and
`leftTrace f = tr_V(K f)`. These agree whenever `q - q⁻¹ ≠ 0`, by
`trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp`, so the pivotal structure is spherical. The
quantum dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`.

These structures depend on the explicit bijectivity of the antipode and on the choice of `K⁻¹`,
so they are definitions installed locally in each statement, not global instances.

## Main definitions

* `TauCeti.UqSl2.rigidCategory`: the rigid structure on finite-dimensional modules.
* `TauCeti.UqSl2.pivotalCategory`: the pivotal structure given by `K⁻¹`.

## Main results

* `TauCeti.UqSl2.dualEquiv_pivotalIsoApp_hom_apply`: the pivot sends `v` to `φ ↦ φ(K⁻¹ v)`.
* `TauCeti.UqSl2.rightTrace_eq_smul`, `TauCeti.UqSl2.leftTrace_eq_smul`: the pivotal traces are
  `tr_V(K⁻¹ f)` and `tr_V(K f)`.
* `TauCeti.UqSl2.sphericalCategory`: the pivotal structure is spherical for `q - q⁻¹ ≠ 0`.
* `TauCeti.UqSl2.rightDim_ladderModule`, `TauCeti.UqSl2.leftDim_ladderModule`,
  `TauCeti.UqSl2.quantumDim_ladderModule`: the dimensions of `L_m^ε` are `ε [m + 1]_q`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for quantum traces
  and quantum dimensions of modules over Hopf algebras.
* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the rank-one Hopf convention and the
  modules `L_m^ε`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- The rigid structure on finite-dimensional `UqSl2 q`-modules: the right dual of a module is its
contragredient through the antipode, and its left dual is its contragredient through the inverse
of the antipode. -/
abbrev rigidCategory : RigidCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) :=
  FiniteHopfModuleCat.rigidCategory (antipode_bijective q)

/-- The pivotal structure on finite-dimensional `UqSl2 q`-modules given by the group-like
element `K⁻¹`, whose components are `v ↦ (φ ↦ φ(K⁻¹ v))`. -/
abbrev pivotalCategory :
    letI := rigidCategory q
    PivotalCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) :=
  FiniteHopfModuleCat.pivotalCategory (g := (kUnit q)⁻¹)
    (fun x => by simpa using antipode_antipode q x) (kUnit_inv (q := q) ▸ isGroupLikeElem_kInv q)

variable {q}

/-- The pivot of a finite-dimensional module `V` sends `v` to the functional `φ ↦ φ(K⁻¹ v)` on
the contragredient. -/
theorem dualEquiv_pivotalIsoApp_hom_apply (V : FiniteHopfModuleCat ℂ (UqSl2 q)) (v : V)
    (φ : (Vᘁ : FiniteHopfModuleCat ℂ (UqSl2 q))) :
    letI := rigidCategory q
    letI := pivotalCategory q
    BialgebraModule.dualEquiv ℂ (UqSl2 q) (Vᘁ : FiniteHopfModuleCat ℂ (UqSl2 q))
        ((pivotalIsoApp V).hom.hom.hom v) φ =
      BialgebraModule.dualEquiv ℂ (UqSl2 q) V φ (kInv q • v) := by
  rw [FiniteHopfModuleCat.pivotalIsoApp_pivotalCategory,
    FiniteHopfModuleCat.dualEquiv_unitEvalIso_hom_apply, kUnit_inv]

/-- The right trace of an endomorphism `f` of a finite-dimensional module `V` is the trace of
`K⁻¹ f` on `V`. -/
theorem rightTrace_eq_smul {V : FiniteHopfModuleCat ℂ (UqSl2 q)} (f : V ⟶ V) :
    letI := rigidCategory q
    letI := pivotalCategory q
    rightTrace f =
      LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V (kInv q) ∘ₗ f.hom.hom.restrictScalars ℂ) •
        𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  refine (FiniteHopfModuleCat.rightTrace_eq_smul _ _ f).trans ?_
  rw [kUnit_inv]

/-- The left trace of an endomorphism `f` of a finite-dimensional module `V` is the trace of
`K f` on `V`. -/
theorem leftTrace_eq_smul {V : FiniteHopfModuleCat ℂ (UqSl2 q)} (f : V ⟶ V) :
    letI := rigidCategory q
    letI := pivotalCategory q
    leftTrace f =
      LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V (k q) ∘ₗ f.hom.hom.restrictScalars ℂ) •
        𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  refine (FiniteHopfModuleCat.leftTrace_eq_smul _ _ f).trans ?_
  rw [inv_inv, kUnit_val]

variable (q) in
/-- For `q - q⁻¹ ≠ 0`, the pivotal structure given by `K⁻¹` is spherical: the left and right
traces `tr_V(K f)` and `tr_V(K⁻¹ f)` of every module endomorphism agree. -/
theorem sphericalCategory (hq : q - q⁻¹ ≠ 0) :
    letI := rigidCategory q
    letI := pivotalCategory q
    SphericalCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) := by
  let := rigidCategory q
  let := pivotalCategory q
  refine ⟨fun f => ?_⟩
  rw [leftTrace_eq_smul, rightTrace_eq_smul, trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp hq]

/-- The trace of an element of `UqSl2 q` on a finite-dimensional module isomorphic to `L_m^ε` is
its trace through the ladder representation. -/
private theorem trace_lsmul_eq_trace_rep {m : ℕ} {ε : ℤˣ} {V : FiniteHopfModuleCat ℂ (UqSl2 q)}
    (e : V ≃ₗ[UqSl2 q] LadderModule q m ε) (a : UqSl2 q) :
    LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V a) =
      LinearMap.trace ℂ _ (LadderModule.rep q m ε a) := by
  rw [← LinearMap.trace_conj' _ (e.restrictScalars ℂ)]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, ← LadderModule.smul_def]

/-- The right dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
theorem rightDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := rigidCategory q
    letI := pivotalCategory q
    rightDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := rigidCategory q
  let := pivotalCategory q
  rw [← rightTrace_id, rightTrace_eq_smul, FiniteHopfModuleCat.hom_hom_id,
    LinearMap.restrictScalars_id, LinearMap.comp_id]
  exact congrArg (· • _) ((trace_lsmul_eq_trace_rep (LinearEquiv.refl _ _) (kInv q)).trans
    (LadderModule.trace_rep_kInv hq))

/-- The left dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
theorem leftDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := rigidCategory q
    letI := pivotalCategory q
    leftDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := rigidCategory q
  let := pivotalCategory q
  rw [← leftTrace_id, leftTrace_eq_smul, FiniteHopfModuleCat.hom_hom_id,
    LinearMap.restrictScalars_id, LinearMap.comp_id]
  exact congrArg (· • _) ((trace_lsmul_eq_trace_rep (LinearEquiv.refl _ _) (k q)).trans
    (LadderModule.trace_rep_k hq))

/-- The quantum dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
@[simp] theorem quantumDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := rigidCategory q
    letI := pivotalCategory q
    haveI := sphericalCategory q hq
    quantumDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := rigidCategory q
  let := pivotalCategory q
  have := sphericalCategory q hq
  rw [quantumDim_eq_rightDim, rightDim_ladderModule hq]

end TauCeti.UqSl2
