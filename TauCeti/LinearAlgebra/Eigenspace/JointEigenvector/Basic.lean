/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

import TauCeti.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Joint eigenvectors of commuting semisimple families

The eigenvalue function of a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` is a character: it maps `1` to `1`, is multiplicative, and, for
a group, valued in units, assembling into `MonoidHom.unitHomOfJointEigenvector : G →* Kˣ`.
For an algebra representation it is moreover additive and `R`-linear, assembling into
`AlgHom.eigenvalueHomOfJointEigenvector : A →ₐ[R] K`. This much
needs no division — a nonzero vector cancels over a commutative ring without zero divisors
acting torsion-freely, and on a group multiplicativity exhibits the inverse of `χ g` as
`χ g⁻¹`. Over a commutative domain acting torsion-freely, the joint eigenspaces of any family of
endomorphisms are supremum-independent; over any field, every invariant submodule contained in the
sum of the joint eigenspaces decomposes as the supremum of its intersections with them. This
yields the simultaneous-diagonalization toolkit for a commuting family: the joint eigenspaces span
in finite dimension when every member is diagonalizable over any field (and hence when every member
is semisimple over an algebraically closed field), and over an algebraically closed field any
finite-dimensional invariant submodule on which the restricted operators pairwise commute and are
semisimple decomposes likewise (whereas over an arbitrary field, decomposition holds for any
invariant submodule contained in the sum of the joint eigenspaces).

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
* `LinearMap.dualOfJointEigenvector`: the eigenvalue function of a nonzero joint eigenvector of a
  linear family of endomorphisms `H →ₗ[K] Module.End K V`, as a linear form `Module.Dual K H`.
* `iSupIndep_iInf_eigenspace` (and `iSupIndep_iInf_eigenspace_unitHom`): over a commutative domain
  acting torsion-freely, the joint eigenspaces of any family of endomorphisms are
  supremum-independent, with no commutation, semisimplicity, finite-dimensionality, or
  algebraic-closedness hypothesis.
* `iSup_iInf_eigenspace_eq_top_of_iSup_eigenspace_eq_top`,
  `iSup_iInf_eigenspace_eq_top_of_isSemisimple`,
  `iSup_inf_iInf_eigenspace_of_invariant`: in finite dimension, the joint eigenspaces of a
  pairwise-commuting family exhaust the space when each member is diagonalizable (over any field)
  or semisimple (over an algebraically closed field), and over an algebraically closed field a
  finite-dimensional invariant submodule on which the restricted endomorphisms pairwise commute and
  are semisimple decomposes likewise — with the character-indexed forms (`…_unitHom…`) for group
  representations.
* `Submodule.inf_iSup_iInf_eigenspace_eq_of_forall_mapsTo`,
  `Submodule.iSup_inf_iInf_eigenspace_eq_of_le`: over any field (with no commutation,
  semisimplicity, finite-dimensionality, or algebraic-closedness hypothesis), the intersection of
  an invariant submodule with the sum of the joint eigenspaces of any family of endomorphisms is
  the supremum of its intersections with them.
* `iInf_eigenspace_eq_of_iSup_eq_top`, `iInf_eigenspace_eq_bot_of_iSup_eq_top`: if spanning
  summands carry pairwise distinct joint scalars of any family of endomorphisms, every summand is
  a joint eigenspace, and every other joint eigenspace is zero.
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

Group actions have nonzero joint eigenvalues over any commutative ring. Over a commutative
ring with cancellation acting torsion-freely, a nonzero vector cancels, so the eigenvalue
function also assembles into a homomorphism.
-/

section GroupScalars

variable [CommRing K] [Module K V] [Group G]

/-- The eigenvalues of a nonzero joint eigenvector of a group representation are nonzero,
since each group element acts injectively. No cancellation or torsion-freeness is needed. -/
lemma _root_.MonoidHom.eigenvalue_ne_zero_of_jointEigenvector
    (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    χ g ≠ 0 := by
  intro hχ
  apply hv
  apply ((Module.End.isUnit_iff _).mp ((Group.isUnit g).map ρ)).injective
  simpa [hχ] using Module.End.mem_eigenspace_iff.mp (hv_mem g)

end GroupScalars

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
  rw [Module.End.mem_eigenspace_iff, map_one, one_apply_eq_self] at h1
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
  rw [← h, mul_apply_eq_comp, Module.End.mem_eigenspace_iff.mp (hv_mem g₂), map_smul,
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

section LinearMap

variable {H : Type*} [AddCommMonoid H] [Module K H]

/-- Given a joint eigenvector `v ≠ 0` for a linear family of endomorphisms
`ρ : H →ₗ[K] Module.End K V`, the eigenvalue function `χ : H → K` is a `K`-linear form. -/
def _root_.LinearMap.dualOfJointEigenvector (ρ : H →ₗ[K] Module.End K V) (χ : H → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ x, v ∈ (ρ x).eigenspace (χ x)) : Module.Dual K H where
  toFun := χ
  map_add' x y := (smul_left_inj hv).mp <| by
    rw [← Module.End.mem_eigenspace_iff.mp (hv_mem (x + y)), add_smul,
      ← Module.End.mem_eigenspace_iff.mp (hv_mem x),
      ← Module.End.mem_eigenspace_iff.mp (hv_mem y), map_add, LinearMap.add_apply]
  map_smul' c x := (smul_left_inj hv).mp <| by
    rw [← Module.End.mem_eigenspace_iff.mp (hv_mem (c • x)), RingHom.id_apply, smul_eq_mul,
      mul_smul, ← Module.End.mem_eigenspace_iff.mp (hv_mem x), map_smul, LinearMap.smul_apply]

@[simp]
lemma _root_.LinearMap.dualOfJointEigenvector_apply (ρ : H →ₗ[K] Module.End K V) (χ : H → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ x, v ∈ (ρ x).eigenspace (χ x)) (x : H) :
    ρ.dualOfJointEigenvector χ v hv hv_mem x = χ x := (rfl)

/-- If the joint eigenspace of an eigenvalue function `χ` of a linear family
`ρ : H →ₗ[K] Module.End K V` is nonzero, then `χ` is (the underlying function of) a linear form
`Module.Dual K H`. -/
lemma exists_dual_of_iInf_eigenspace_ne_bot {ρ : H →ₗ[K] Module.End K V}
    {χ : H → K} (hχ : ⨅ x, (ρ x).eigenspace (χ x) ≠ ⊥) :
    ∃ μ : Module.Dual K H, ⇑μ = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨ρ.dualOfJointEigenvector χ v hv_ne ((Submodule.mem_iInf _).mp hv_mem), rfl⟩

/-- A family of submodules lying in the joint eigenspaces of a linear family
`ρ : H →ₗ[K] Module.End K V` has the same supremum over `Module.Dual K H` as over all
eigenvalue functions `H → K`. -/
lemma iSup_dual_eq_iSup {ρ : H →ₗ[K] Module.End K V}
    (F : (H → K) → Submodule K V) (hF : ∀ χ, F χ ≤ ⨅ x, (ρ x).eigenspace (χ x)) :
    (⨆ μ : Module.Dual K H, F ⇑μ) = ⨆ χ, F χ := by
  refine le_antisymm (iSup_le fun μ ↦ le_iSup F _) (iSup_le fun χ ↦ ?_)
  by_cases hχ : F χ = ⊥
  · simp [hχ]
  · obtain ⟨μ, rfl⟩ := exists_dual_of_iInf_eigenspace_ne_bot (ρ := ρ)
      fun h ↦ hχ (eq_bot_iff.mpr (h ▸ hF χ))
    exact le_iSup (fun ψ : Module.Dual K H ↦ F ⇑ψ) μ

end LinearMap

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

/-- **Summands of a spanning family with distinct joint scalars are joint eigenspaces.** If the
`W j` span `V`, every `W j` consists of joint eigenvectors of the family `f` with eigenvalues
`g j`, and `g` is injective, then the joint eigenspace of `f` for `g k` is exactly `W k`. This is
the joint form of the eigenspace case (`n = 1`) of `Module.End.genEigenspace_eq_of_iSup_eq_top`:
the scalars of a single operator need not separate the summands, only those of the whole family. -/
theorem iInf_eigenspace_eq_of_iSup_eq_top {ι κ : Type*} (f : ι → Module.End K V)
    {W : κ → Submodule K V} {g : κ → ι → K} (hW : ∀ j, W j ≤ ⨅ i, (f i).eigenspace (g j i))
    (htop : ⨆ j, W j = ⊤) (hg : Function.Injective g) (k : κ) :
    ⨅ i, (f i).eigenspace (g k i) = W k :=
  (congrFun (((iSupIndep_iInf_eigenspace f).comp hg).le_iff_eq_of_iSup_eq_top htop |>.mp hW)
    k).symm

/-- **Joint eigenvalues outside a spanning family of joint eigenspaces do not occur.** If the
`W j` span `V` and every `W j` consists of joint eigenvectors of the family `f` with eigenvalues
`g j`, then the joint eigenspace of `f` for any eigenvalue function `χ` that is not some `g j`
is zero. -/
theorem iInf_eigenspace_eq_bot_of_iSup_eq_top {ι κ : Type*} (f : ι → Module.End K V)
    {W : κ → Submodule K V} {g : κ → ι → K} (hW : ∀ j, W j ≤ ⨅ i, (f i).eigenspace (g j i))
    (htop : ⨆ j, W j = ⊤) {χ : ι → K} (hχ : χ ∉ Set.range g) :
    ⨅ i, (f i).eigenspace (χ i) = ⊥ := by
  have hle : ⊤ ≤ ⨆ (c) (_ : c ≠ χ), ⨅ i, (f i).eigenspace (c i) :=
    htop ▸ iSup_le fun j ↦ (hW j).trans (le_iSup₂_of_le (g j) (fun h ↦ hχ ⟨j, h⟩) le_rfl)
  exact disjoint_top.mp ((iSupIndep_iInf_eigenspace f χ).mono_right hle)

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

/-! ### Invariant submodules of a sum of joint eigenspaces

Over any field, with no commutation, semisimplicity, finite-dimensionality, or algebraic-closedness
hypothesis, membership of a finite sum of distinct joint-weight components in an invariant subspace
forces membership of each component, even if the joint eigenspaces do not span the ambient space.
Consequently, the intersection of an invariant subspace with the sum of all joint eigenspaces is
spanned by its intersections with the individual joint eigenspaces.
-/

section InvariantSubmodule

variable [Field K] [Module K V]

/-- **Joint-eigenvector components of an invariant subspace.** Over any field, if a finite sum of
joint eigenvectors for pairwise distinct eigenvalue functions (indexed by a finset `s`) lies in an
`f`-invariant submodule `p`, then every summand lies in `p`. -/
theorem mem_of_sum_mem_of_forall_mem_iInf_eigenspace {ι : Type*} (f : ι → Module.End K V)
    {p : Submodule K V} (hp : ∀ i, Set.MapsTo (f i) p p) {s : Finset (ι → K)} {u : (ι → K) → V}
    (hu : ∀ χ ∈ s, u χ ∈ ⨅ i, (f i).eigenspace (χ i)) (hsum : ∑ χ ∈ s, u χ ∈ p)
    {χ : ι → K} (hχ : χ ∈ s) : u χ ∈ p := by
  let f' : ι → Module.End K (V ⧸ p) := fun i ↦ p.mapQ p (f i) fun _ hx ↦ hp i hx
  have hu' : ∀ ψ ∈ s, p.mkQ (u ψ) ∈ ⨅ i, (f' i).eigenspace (ψ i) := fun ψ hψ ↦
    (Submodule.mem_iInf _).mpr fun i ↦ Module.End.mem_eigenspace_iff.mpr <| by
      dsimp only [f']
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply,
        Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp (hu ψ hψ) i),
        Submodule.Quotient.mk_smul]
  have hsum' : ∑ ψ ∈ s, p.mkQ (u ψ) = 0 := by
    rw [← map_sum, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsum
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (iSupIndep_iInf_eigenspace f') s (fun ψ ↦ p.mkQ (u ψ)) hu' hsum' χ hχ
  exact (Submodule.Quotient.mk_eq_zero p).mp hzero

/-- **Intersecting an invariant submodule with a sum of joint eigenspaces.** Over any field, the
part of an `f`-invariant submodule `p` lying in the sum of the joint eigenspaces of `f` is spanned
by its intersections with those joint eigenspaces. -/
theorem _root_.Submodule.inf_iSup_iInf_eigenspace_eq_of_forall_mapsTo {ι : Type*}
    {f : ι → Module.End K V} (p : Submodule K V) (hp : ∀ i, Set.MapsTo (f i) p p) :
    p ⊓ (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) =
      ⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i) := by
  classical
  refine le_antisymm ?_
    (iSup_le fun χ ↦ inf_le_inf_left p (le_iSup (fun ψ : ι → K ↦ ⨅ i, (f i).eigenspace (ψ i)) χ))
  rintro x ⟨hxp, hxs⟩
  obtain ⟨u, hu, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hxs
  rw [Finsupp.sum]
  exact Submodule.sum_mem _ fun χ hχ ↦ Submodule.mem_iSup_of_mem χ
    ⟨mem_of_sum_mem_of_forall_mem_iInf_eigenspace f hp (fun ψ _ ↦ hu ψ) hxp hχ, hu χ⟩

/-- **Decomposing an invariant submodule contained in the sum of joint eigenspaces.** Over any
field, an `f`-invariant submodule contained in the sum of the joint eigenspaces of `f` is the
supremum of its intersections with them. -/
theorem _root_.Submodule.iSup_inf_iInf_eigenspace_eq_of_le {ι : Type*}
    {f : ι → Module.End K V} (p : Submodule K V) (hp : ∀ i, Set.MapsTo (f i) p p)
    (hle : p ≤ ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p :=
  (p.inf_iSup_iInf_eigenspace_eq_of_forall_mapsTo hp).symm.trans (inf_eq_left.mpr hle)

end InvariantSubmodule

/-! ### Simultaneous diagonalization

The spanning statements for diagonalizable families over any field, and for semisimple families
over an algebraically closed field.
-/

section FieldScalars

variable [Field K] [Module K V]

/-- **Simultaneous diagonalization.** In finite dimension, the joint eigenspaces of a
pairwise-commuting family of diagonalizable endomorphisms exhaust the space. -/
lemma iSup_iInf_eigenspace_eq_top_of_iSup_eigenspace_eq_top [FiniteDimensional K V] {ι : Type*}
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, (f i).eigenspace μ = ⊤) :
    (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (isSemisimple_of_iSup_eigenspace_eq_top (hdiag i)).isFinitelySemisimple
      |>.maxGenEigenspace_eq_eigenspace μ
  simpa only [heq] using
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      hcomm fun i ↦ by simpa only [heq] using hdiag i

variable [IsAlgClosed K]

/-- Over an algebraically closed field and in finite dimension, the joint eigenspaces of a
pairwise-commuting family of semisimple endomorphisms exhaust the space. -/
lemma iSup_iInf_eigenspace_eq_top_of_isSemisimple [FiniteDimensional K V] {ι : Type*}
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ :=
  iSup_iInf_eigenspace_eq_top_of_iSup_eigenspace_eq_top f hcomm fun i ↦
    (hss i).iSup_eigenspace_eq_top

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

section FourierProjector

variable [CommRing K] [Module K V] [Group G] [Finite G]

-- The averaging sums below need a `Fintype G`, and it has to stay file-local: as a global
-- instance (even a `private` one, which still ends up in the environment the linters see) it
-- reads as `[Finite α] → Fintype α` for *every* type `α`, because `G`'s group structure
-- is not used, and so perturbs instance resolution and `simp` normal forms library-wide.
attribute [local instance] Fintype.ofFinite

variable {ρ : G →* Module.End K V}

/-- The Fourier projector for `χ₀`, applied to a vector: the character idempotent
`TauCeti.charIdempotent χ₀` acting through `ρ`. -/
private def fourierComponent (χ₀ : G →* Kˣ) (v : V) : V :=
  Representation.asAlgebraHom ρ (charIdempotent χ₀) v

variable (ρ) in
private lemma fourierComponent_mem (χ₀ : G →* Kˣ) (v : V) (g : G) :
    fourierComponent (ρ := ρ) χ₀ v ∈ (ρ g).eigenspace (χ₀ g) := by
  rw [fourierComponent]
  exact Module.End.mem_eigenspace_iff.2 <|
    (Representation.mem_charEigenspace_iff ρ χ₀).1
      (Representation.asAlgebraHom_charIdempotent_apply_mem ρ χ₀ v) g

end FourierProjector

section FourierDecomposition

variable [CommRing K] [IsDomain K] [Module K V] [CommGroup G] [Finite G]

attribute [local instance] Fintype.ofFinite

variable {ρ : G →* Module.End K V} [HasEnoughRootsOfUnity K (Monoid.exponent G)]

private lemma sum_fourierComponent (hunit : IsUnit (Nat.card G : K)) (v : V) :
    ∑ χ₀ : G →* Kˣ, fourierComponent (ρ := ρ) χ₀ v = v := by
  simp_rw [fourierComponent, ← LinearMap.sum_apply, ← map_sum, sum_charIdempotent hunit, map_one,
    one_apply_eq_self]

omit [Finite G] in
/-- **Unconditional decomposition of an invariant submodule**: the character projectors
preserve every `ρ`-invariant submodule, so it is the supremum of its intersections with
the joint eigenspaces — again with no finite-dimensionality hypothesis. The group is finite
because `Nat.card G` is a unit. -/
theorem iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
    (hcard : IsUnit (Nat.card G : K))
    (p : Submodule K V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  have : Finite G := TauCeti.finite_of_natCast_card_ne_zero hcard.ne_zero
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun v hv ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) hcard v]
  refine Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀ ?_
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g ↦
    fourierComponent_mem ρ χ₀ v g⟩
  rw [fourierComponent, Representation.asAlgebraHom_charIdempotent]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun d _ ↦
    Submodule.smul_mem _ _ (hp d v hv))

omit [Finite G] in
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
