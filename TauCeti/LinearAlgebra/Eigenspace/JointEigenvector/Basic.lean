/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Joint eigenvectors of commuting semisimple families

The eigenvalue function of a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` is a character: it maps `1` to `1`, is multiplicative, and, for
a group, valued in units, assembling into `MonoidHom.unitHomOfJointEigenvector : G →* Kˣ`.
For an algebra representation it is moreover additive and `R`-linear, assembling into
`AlgHom.eigenvalueHomOfJointEigenvector : A →ₐ[R] K`. This much
needs no division — a nonzero vector cancels over a commutative ring without zero divisors
acting torsion-freely, and on a group multiplicativity exhibits the inverse of `χ g` as
`χ g⁻¹`. This yields the simultaneous-diagonalization toolkit for a commuting family of
semisimple endomorphisms: the joint eigenspaces are supremum-independent, they span (over an
algebraically closed field, in finite dimension), and every invariant submodule is the
supremum of its intersections with them.

When `G` is a *finite commutative group* there is a second, unconditional route to the same
spanning statements. Averaging against the characters of `G` produces Fourier projectors onto
the joint eigenspaces, so they exhaust the whole space — and cut out every invariant submodule —
with no algebraic-closedness, finite-dimensionality or semisimplicity hypothesis; all that is
needed is enough roots of unity in `K` and `Nat.card G` invertible there.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted as
representation-theoretic infrastructure with no modular-forms dependence: there `G` is the
group `(ZMod N)ˣ` of diamond operators, and the character eigenspaces are the nebentypus
components of `M_k(Γ₁(N))`.

## Main results

* `MonoidHom.unitHomOfJointEigenvector`: the eigenvalue function of a nonzero joint eigenvector of a
  group representation, as a monoid homomorphism `G →* Kˣ`.
* `AlgHom.eigenvalueHomOfJointEigenvector`: the eigenvalue function of a nonzero joint
  eigenvector of an algebra representation, as an algebra homomorphism `A →ₐ[R] K`.
* `iSupIndep_iInf_eigenspace`,
  `iSup_iInf_eigenspace_eq_top_of_isSemisimple`,
  `iSup_inf_iInf_eigenspace_of_invariant`: joint eigenspaces of a commuting family are
  independent (with no further hypotheses), exhaust the space when semisimple, and
  decompose every invariant submodule — with the character-indexed forms (`…_unitHom…`)
  for group representations.
* `MonoidHom.finite_nonzeroJointWeights`, `MonoidHom.natCard_nonzeroJointWeights_le_finrank`:
  a representation on a finite module over a domain has finitely many nonzero joint weights,
  with their number bounded by its rank.
* `iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup`,
  `iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup`: for a finite commutative `G`
  with `[HasEnoughRootsOfUnity K (Monoid.exponent G)]` and `IsUnit (Nat.card G : K)`, the
  character eigenspaces span the whole space, and every invariant submodule is the supremum of
  its intersections with them — proved by finite-group Fourier projectors, so neither
  semisimplicity nor finite dimension is assumed.
-/

public section

noncomputable section

namespace TauCeti

variable {G K V : Type*} [AddCommGroup V]

/-! ### The restriction bridge -/

section BridgeScalars

variable [CommRing K] [Module K V]

/-- **The restriction bridge for joint eigenspaces**: for a family of endomorphisms mapping a
submodule `p` into itself, the part of a joint eigenspace lying in `p` is the image of the
joint eigenspace of the restricted family. This is the eigenspace analogue of
`Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`. -/
theorem _root_.Submodule.inf_iInf_eigenspace_of_forall_mapsTo {ι : Type*}
    {f : ι → Module.End K V} (p : Submodule K V) (hp : ∀ i, Set.MapsTo (f i) p p)
    (χ : ι → K) :
    p ⊓ ⨅ i, (f i).eigenspace (χ i) =
      (⨅ i, Module.End.eigenspace ((f i).restrict (hp i)) (χ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [Module.End.eigenspace, inf_iInf, p.inf_genEigenspace _ (hp _),
      Submodule.map_iInf _ p.injective_subtype]

end BridgeScalars

/-! ### Eigenvalues of a joint eigenvector

Over a commutative ring with cancellation acting torsion-freely, so that a nonzero vector
cancels.
-/

section CancelScalars

variable [CommRing K] [IsCancelMulZero K] [Module K V] [Module.IsTorsionFree K V]

section MulOne

variable [MulOne G]

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalue at the
identity is `1`. -/
lemma _root_.MonoidHom.eigenvalue_one_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : χ 1 = 1 := by
  have h1 := hv_mem 1
  rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at h1
  exact (smul_left_inj hv).mp (by rw [← h1, one_smul])

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalues are
multiplicative: `χ (g₁ * g₂) = χ g₁ * χ g₂`. -/
lemma _root_.MonoidHom.eigenvalue_mul_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g₁ g₂ : G) :
    χ (g₁ * g₂) = χ g₁ * χ g₂ := by
  have h := hv_mem (g₁ * g₂)
  rw [Module.End.mem_eigenspace_iff, map_mul] at h
  refine (smul_left_inj hv).mp ?_
  rw [← h, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp (hv_mem g₂), map_smul,
    Module.End.mem_eigenspace_iff.mp (hv_mem g₁), smul_smul, mul_comm (χ g₂) (χ g₁)]

end MulOne

section Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Algebra R K] [Module R V]
  [IsScalarTower R K V]

/-- Given a joint eigenvector `v ≠ 0` for an algebra representation
`ρ : A →ₐ[R] Module.End K V`, the eigenvalue function `χ : A → K` is an `R`-algebra
homomorphism. -/
def _root_.AlgHom.eigenvalueHomOfJointEigenvector (ρ : A →ₐ[R] Module.End K V) (χ : A → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ a, v ∈ (ρ a).eigenspace (χ a)) : A →ₐ[R] K where
  toFun := χ
  map_one' := ρ.toMonoidHom.eigenvalue_one_of_jointEigenvector χ v hv hv_mem
  map_mul' := ρ.toMonoidHom.eigenvalue_mul_of_jointEigenvector χ v hv hv_mem
  map_zero' := (smul_left_inj hv).mp <| by
    rw [← Module.End.mem_eigenspace_iff.mp (hv_mem 0), map_zero, zero_smul, LinearMap.zero_apply]
  map_add' a b := (smul_left_inj hv).mp <| by
    rw [← Module.End.mem_eigenspace_iff.mp (hv_mem (a + b)), add_smul,
      ← Module.End.mem_eigenspace_iff.mp (hv_mem a), ← Module.End.mem_eigenspace_iff.mp (hv_mem b),
      map_add, LinearMap.add_apply]
  commutes' r := (smul_left_inj hv).mp <| by
    rw [← Module.End.mem_eigenspace_iff.mp (hv_mem _), AlgHom.commutes,
      Module.algebraMap_end_apply, algebraMap_smul]

@[simp]
lemma _root_.AlgHom.eigenvalueHomOfJointEigenvector_apply (ρ : A →ₐ[R] Module.End K V)
    (χ : A → K) (v : V) (hv : v ≠ 0) (hv_mem : ∀ a, v ∈ (ρ a).eigenspace (χ a)) (a : A) :
    ρ.eigenvalueHomOfJointEigenvector χ v hv hv_mem a = χ a := (rfl)

end Algebra

section Group

variable [Group G]

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a group `G`, the eigenvalue function `χ : G → K`
factors through a monoid homomorphism `G →* Kˣ`. -/
def _root_.MonoidHom.unitHomOfJointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : G →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun := χ
      map_one' := ρ.eigenvalue_one_of_jointEigenvector χ v hv hv_mem
      map_mul' := ρ.eigenvalue_mul_of_jointEigenvector χ v hv hv_mem }

@[simp]
lemma _root_.MonoidHom.unitHomOfJointEigenvector_apply (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((ρ.unitHomOfJointEigenvector χ v hv hv_mem g) : K) = χ g := (rfl)

/-- The eigenvalues of a nonzero joint eigenvector of a group representation are
nonzero. -/
lemma _root_.MonoidHom.eigenvalue_ne_zero_of_jointEigenvector
    (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    χ g ≠ 0 := by
  have := nontrivial_of_ne v 0 hv
  have := Module.nontrivial K V
  simpa using (ρ.unitHomOfJointEigenvector χ v hv hv_mem g).ne_zero

/-- If the joint eigenspace of an eigenvalue function `χ` of a group representation is
nonzero, then `χ` is (the underlying function of) a character `G →* Kˣ`. -/
lemma exists_unitHom_of_iInf_eigenspace_ne_bot {ρ : G →* Module.End K V}
    {χ : G → K} (hχ : ⨅ g, (ρ g).eigenspace (χ g) ≠ ⊥) :
    ∃ χ₀ : G →* Kˣ, (fun g ↦ ((χ₀ g) : K)) = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨ρ.unitHomOfJointEigenvector χ v hv_ne ((Submodule.mem_iInf _).mp hv_mem), rfl⟩

/-- A family of submodules lying in the joint eigenspaces of a group representation has the
same supremum over the characters `G →* Kˣ` as over all eigenvalue functions `G → K`. -/
private lemma iSup_unitHom_eq_iSup {ρ : G →* Module.End K V}
    (F : (G → K) → Submodule K V) (hF : ∀ χ, F χ ≤ ⨅ g, (ρ g).eigenspace (χ g)) :
    ⨆ χ₀ : G →* Kˣ, F (fun g ↦ χ₀ g) = ⨆ χ, F χ := by
  refine le_antisymm (iSup_le fun χ₀ ↦ le_iSup F _) (iSup_le fun χ ↦ ?_)
  by_cases hχ : F χ = ⊥
  · simp [hχ]
  · obtain ⟨χ₀, rfl⟩ := exists_unitHom_of_iInf_eigenspace_ne_bot (ρ := ρ)
      fun h ↦ hχ (eq_bot_iff.mpr (h ▸ hF χ))
    exact le_iSup (fun ψ : G →* Kˣ ↦ F fun g ↦ ψ g) χ₀

end Group

end CancelScalars

/-! ### Independence of joint eigenspaces

Over a commutative domain acting torsion-freely.
-/

section DomainScalars

variable [CommRing K] [IsDomain K] [Module K V] [Module.IsTorsionFree K V]

/-- The joint eigenspaces of **any** family of endomorphisms, indexed by their eigenvalue
functions, are supremum-independent — no commutation and no semisimplicity. -/
lemma iSupIndep_iInf_eigenspace {ι : Type*} (f : ι → Module.End K V) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) :=
  iSupIndep.iInf (fun i ↦ (f i).eigenspace) fun i ↦ (f i).eigenspaces_iSupIndep

variable [MulOne G] {ρ : G →* Module.End K V}

/-- **Character-indexed independence** of the joint eigenspaces, for any representation. -/
lemma iSupIndep_iInf_eigenspace_unitHom :
    iSupIndep fun χ₀ : G →* Kˣ ↦ ⨅ g, (ρ g).eigenspace (χ₀ g) :=
  (iSupIndep_iInf_eigenspace (fun g ↦ ρ g)).comp
    fun _ _ h ↦ MonoidHom.ext fun g ↦ Units.ext (congr_fun h g)

/-- A representation on a finite module has only finitely many characters with nonzero joint
weight space. -/
instance _root_.MonoidHom.finite_nonzeroJointWeights [Module.Finite K V]
    (ρ : G →* Module.End K V) :
    Finite {χ : G →* Kˣ // (⨅ g : G, (ρ g).eigenspace (χ g)) ≠ ⊥} :=
  let _ := iSupIndep_iInf_eigenspace_unitHom (ρ := ρ).fintypeNeBotOfFiniteDimensional
  inferInstance

/-- The number of characters with nonzero joint weight space in a representation on a finite
module is bounded by the rank of the module. -/
theorem _root_.MonoidHom.natCard_nonzeroJointWeights_le_finrank [Module.Finite K V]
    (ρ : G →* Module.End K V) :
    Nat.card {χ : G →* Kˣ // (⨅ g : G, (ρ g).eigenspace (χ g)) ≠ ⊥} ≤
      Module.finrank K V := by
  let _ := iSupIndep_iInf_eigenspace_unitHom (ρ := ρ).fintypeNeBotOfFiniteDimensional
  rw [Nat.card_eq_fintype_card]
  exact iSupIndep_iInf_eigenspace_unitHom.subtype_ne_bot_le_finrank

end DomainScalars

/-! ### Simultaneous diagonalization

The spanning statements for semisimple families, over an algebraically closed field.
-/

section FieldScalars

variable [Field K] [IsAlgClosed K] [Module K V]

/-- Over an algebraically closed field and in finite dimension, the joint eigenspaces of a
pairwise-commuting family of semisimple endomorphisms exhaust the space. -/
lemma iSup_iInf_eigenspace_eq_top_of_isSemisimple [FiniteDimensional K V] {ι : Type*}
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simpa only [heq] using
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      hcomm fun i ↦ by simpa only [heq] using (hss i).iSup_eigenspace_eq_top

/-- A finite-dimensional submodule invariant under a pairwise-commuting family of
endomorphisms whose **restrictions** to it are semisimple is the supremum of its
intersections with the joint eigenspaces: the restricted family diagonalizes, with no
assumption on the ambient operators. -/
lemma iSup_inf_iInf_eigenspace_of_invariant {ι : Type*} (f : ι → Module.End K V)
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ i, ∀ x ∈ p, f i x ∈ p)
    (hcomm : Pairwise fun i j ↦ Commute ((f i).restrict (hp i)) ((f j).restrict (hp j)))
    (hss : ∀ i, Module.End.IsSemisimple ((f i).restrict (hp i))) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  simp_rw [fun χ ↦ Submodule.inf_iInf_eigenspace_of_forall_mapsTo (f := f) p hp χ,
    ← Submodule.map_iSup,
    iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun i ↦ (f i).restrict (hp i)) hcomm hss,
    Submodule.map_top, Submodule.range_subtype]

variable [Group G] {ρ : G →* Module.End K V}

/-- **Character-indexed spanning**: for a commuting semisimple representation of a group
over an algebraically closed field, in finite dimension, the joint eigenspaces indexed by
characters `G →* Kˣ` exhaust the space. -/
lemma iSup_iInf_eigenspace_unitHom_eq_top [FiniteDimensional K V]
    (hcomm : Pairwise fun g₁ g₂ ↦ Commute (ρ g₁) (ρ g₂))
    (hss : ∀ g, (ρ g).IsSemisimple) :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ :=
  (iSup_unitHom_eq_iSup (fun χ ↦ ⨅ g, (ρ g).eigenspace (χ g)) fun _ ↦ le_rfl).trans
    (iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun g ↦ ρ g) hcomm hss)

/-- **Character-indexed decomposition of a finite-dimensional invariant submodule**,
assuming only that the restricted representation is semisimple. -/
lemma iSup_inf_iInf_eigenspace_unitHom_of_invariant
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p)
    (hcomm : Pairwise fun g₁ g₂ ↦
      Commute ((ρ g₁).restrict (hp g₁)) ((ρ g₂).restrict (hp g₂)))
    (hss : ∀ g, Module.End.IsSemisimple ((ρ g).restrict (hp g))) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p :=
  (iSup_unitHom_eq_iSup (fun χ ↦ p ⊓ ⨅ g, (ρ g).eigenspace (χ g)) fun _ ↦ inf_le_right).trans
    (iSup_inf_iInf_eigenspace_of_invariant (fun g ↦ ρ g) p hp hcomm hss)

end FieldScalars

/-! ### Unconditional decomposition for finite commutative groups

For a finite commutative group `G` acting through `ρ : G →* Module.End K V` on any module
over a commutative domain with enough roots of unity in which `Nat.card G` is invertible — with
no finite-dimensionality assumption — the classical character projectors
`|G|⁻¹ • ∑ d, χ(d)⁻¹ • ρ d` decompose every vector into joint eigenvectors, so the joint
eigenspaces indexed by `G →* Kˣ` span. -/

section FourierDecomposition

variable [CommRing K] [IsDomain K] [Module K V] [CommGroup G] [Finite G]

-- The averaging sums below need a `Fintype G`, and it has to stay file-local: as a global
-- instance (even a `private` one, which still ends up in the environment the linters see) it
-- reads as `[Finite α] → Fintype α` for *every* type `α`, because `G`'s `CommGroup` argument
-- is not used, and so perturbs instance resolution and `simp` normal forms library-wide.
attribute [local instance] Fintype.ofFinite

open Finset

variable {ρ : G →* Module.End K V}

/-- The Fourier projector for `χ₀`, applied to a vector. -/
private def fourierComponent (χ₀ : G →* Kˣ) (v : V) : V :=
  Ring.inverse (Nat.card G : K) • ∑ d : G, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v

variable (ρ) in
omit [IsDomain K] in
private lemma fourierComponent_mem (χ₀ : G →* Kˣ) (v : V) (g : G) :
    fourierComponent (ρ := ρ) χ₀ v ∈ (ρ g).eigenspace (χ₀ g) := by
  rw [Module.End.mem_eigenspace_iff, fourierComponent, map_smul,
    smul_comm ((χ₀ g : Kˣ) : K) (Ring.inverse (Nat.card G : K))]
  congr 1
  rw [map_sum, smul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun d ↦ by
    simp [smul_smul, mul_comm]

variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

private lemma sum_fourierComponent (hunit : IsUnit (Nat.card G : K)) (v : V) :
    ∑ χ₀ : G →* Kˣ, fourierComponent (ρ := ρ) χ₀ v = v := by
  classical
  simp_rw [fourierComponent, ← smul_sum]
  rw [sum_comm]
  simp_rw [← sum_smul, ← map_inv, CommGroup.sum_monoidHom_apply_eq_ite, inv_eq_one, ite_smul,
    zero_smul, sum_ite_eq', mem_univ, ite_true, map_one, Module.End.one_apply, smul_smul,
    Ring.inverse_mul_cancel _ hunit, one_smul]

/-- **Unconditional decomposition of an invariant submodule**: the character projectors
preserve every `ρ`-invariant submodule, so it is the supremum of its intersections with
the joint eigenspaces — again with no finite-dimensionality hypothesis. -/
theorem iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
    (hcard : IsUnit (Nat.card G : K))
    (p : Submodule K V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun v hv ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) hcard v]
  refine Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀ ?_
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g ↦
    fourierComponent_mem ρ χ₀ v g⟩
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun d _ ↦
    Submodule.smul_mem _ _ (hp d v hv))

/-- **Unconditional character-indexed spanning** for a finite commutative group acting on
an arbitrary module over a commutative domain with enough roots of unity: the classical
character projectors decompose every vector, with no finite-dimensionality or
semisimplicity hypotheses. -/
theorem iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup
    (hcard : IsUnit (Nat.card G : K)) :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ := by
  simpa using iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup (ρ := ρ) hcard ⊤
    fun _ _ _ ↦ Submodule.mem_top

end FourierDecomposition

end TauCeti

end
