/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.SymmetricAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Algebra.HopfAlgebra.Antipode
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Topology.Constructible.Jacobson

/-!
# The closure order on orbits of vectors

Let `G = Spec H` be an affine group over a field `k` acting on a finite-dimensional
representation `M`, and let `TauCeti.Comodule.VectorOrbit k H M` be the set of rational orbits of
`G` in `M`. The orbit of `v` has a geometric image `Oᵥ` (`TauCeti.Comodule.VectorOrbit.image`):
the full topological image of the projective orbit morphism of the line through `(v, 1)` in the
projective completion `P(M × k)` of `M`. Both are defined in
`TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic`.

When `k` is algebraically closed and `G` is of finite type, distinct orbits have distinct images,
and even distinct closures. The *closure order* on orbits,

  `O ≤ O'` if and only if `O ⊆ closure O'`,

is therefore a partial order. An orbit lies strictly below another exactly when its vectors lie
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension.

Invariant polynomial functions in `Sym(M*)^G` pull back to constants along the orbit morphism of
any vector (`TauCeti.Comodule.orbitCoordinates_eq_algebraMap_of_mem_coinvariants`) and therefore
take the same value on every vector in an orbit and in its closure
(`TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_le`). Over any infinite field, a conical orbit —
one closed under nonzero scalar multiplication — contains the origin in its closure
(`TauCeti.Comodule.mem_closure_projectiveOrbitMap_zero_of_forall_smul`,
`TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`).

When an orbit `O` has only finitely many orbits below it in the closure order, the affine chart
`M = {t ≠ 0}` of `P(M × k)` cuts both `closure O` and the boundary `closure O \ O` into the exact
union of the full scheme-point orbit images below `O`
(`TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion_le` and
`TauCeti.Comodule.VectorOrbit.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt`).

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.image_injective`,
  `TauCeti.Comodule.VectorOrbit.closure_image_injective`: orbits are determined by their images,
  and even by the closures of their images.
* `TauCeti.Comodule.VectorOrbit.instPartialOrder`: the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff`, `TauCeti.Comodule.VectorOrbit.mk_lt_mk_iff`:
  the orbit of `w` lies below the orbit of `v` when `w` lies in the closure of the orbit of
  `v`, and strictly below when `w` lies in its boundary.
* `TauCeti.Comodule.VectorOrbit.strictMono_topologicalKrullDim_image`: strictly smaller orbits
  have strictly smaller dimension.
* `TauCeti.Comodule.orbitCoordinates_eq_algebraMap_of_mem_coinvariants`,
  `TauCeti.Comodule.lift_eval_basePointsRepresentation_eq_of_mem_coinvariants`,
  `TauCeti.Comodule.lift_eval_eq_of_mem_closure_projectiveOrbitMap`, and
  `TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_le`: invariant polynomial functions are constant on
  every orbit and its closure.
* `TauCeti.Comodule.mem_closure_projectiveOrbitMap_zero_of_forall_smul` and
  `TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`: conical orbits contain `0` in their
  closure.
* `TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion_le` and
  `TauCeti.Comodule.VectorOrbit.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt`: when the
  lower set of `O` is finite, `closure O` and `closure O \ O` in the affine chart `M` are the
  unions of the full orbit images `O' ≤ O` and `O' < O`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace TauCeti.Comodule

universe u

attribute [local instance] prodTrivial

section Invariants

section Ring

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M] [Module.Finite R M] [Module.Projective R M]

/-- **Invariant polynomial functions pull back to constants along orbit coordinates.**
If `p ∈ Sym(M*)^G` is coinvariant for the contragredient coaction, then `orbitCoordinates m p` is
the constant `algebraMap R H (p(m))` in `H`. No field or reducedness hypothesis is needed. -/
theorem orbitCoordinates_eq_algebraMap_of_mem_coinvariants (m : M)
    {p : SymmetricAlgebra R (Module.Dual R M)}
    (hp : letI := dual R H M; letI := ComoduleAlgebra.symmetricAlgebra R H (Module.Dual R M)
      p ∈ ComoduleAlgebra.coinvariants R H (SymmetricAlgebra R (Module.Dual R M))) :
    orbitCoordinates (H := H) m p =
      algebraMap R H (SymmetricAlgebra.lift (Module.Dual.eval R M m) p) := by
  let _ := dual R H M
  let _ := ComoduleAlgebra.symmetricAlgebra R H (Module.Dual R M)
  let Ψ : SymmetricAlgebra R (Module.Dual R M) ⊗[R] H →ₐ[R] H :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId R H).comp (SymmetricAlgebra.lift (Module.Dual.eval R M m)))
      (AlgHom.id R H) (fun _ _ ↦ Commute.all _ _)
  have hΨ_ι : ∀ z : Module.Dual R M ⊗[R] H,
      Ψ ((SymmetricAlgebra.ι R (Module.Dual R M)).rTensor H z) = dualTensorHom R M H z m := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul φ h =>
      simp [Ψ, Algebra.smul_def]
    | add z₁ z₂ ih₁ ih₂ =>
      simp [map_add, ih₁, ih₂]
  have hcomp : Ψ.comp (symmetricAlgebraCoact R H (Module.Dual R M)) =
      (_root_.HopfAlgebra.antipodeAlgHom R H).comp (orbitCoordinates (H := H) m) := by
    ext φ
    change Ψ (symmetricAlgebraCoact R H (Module.Dual R M)
        (SymmetricAlgebra.ι R (Module.Dual R M) φ)) =
      _root_.HopfAlgebra.antipodeAlgHom R H
        (orbitCoordinates (H := H) m (SymmetricAlgebra.ι R (Module.Dual R M) φ))
    rw [symmetricAlgebraCoact_ι, dual_coact, hΨ_ι, dualTensorHom_dualCoact_apply,
      orbitCoordinates_ι, _root_.HopfAlgebra.antipodeAlgHom_apply]
  have hp' : symmetricAlgebraCoact R H (Module.Dual R M) p = p ⊗ₜ[R] (1 : H) := by
    simpa [ComoduleAlgebra.mem_coinvariants, ComoduleAlgebra.symmetricAlgebra_coact] using hp
  have happ := congrArg (fun f ↦ f p) hcomp
  simp only [AlgHom.comp_apply, _root_.HopfAlgebra.antipodeAlgHom_apply] at happ
  rw [hp'] at happ
  have hval : Ψ (p ⊗ₜ[R] (1 : H)) =
      algebraMap R H (SymmetricAlgebra.lift (Module.Dual.eval R M m) p) := by
    simp [Ψ]
  rw [hval] at happ
  have := congrArg (_root_.HopfAlgebra.antipodeAlgHom R H) happ.symm
  simpa [_root_.HopfAlgebra.antipodeAlgHom_apply, TauCeti.HopfAlgebra.antipode_antipode] using this

/-- **Invariant polynomial functions are constant on rational orbits.** Over any commutative base
ring, a coinvariant polynomial `p ∈ Sym(M*)^G` takes the same value on `g • m` and `m`. -/
theorem lift_eval_basePointsRepresentation_eq_of_mem_coinvariants
    (g : WithConv (H →ₐ[R] R)) (m : M) {p : SymmetricAlgebra R (Module.Dual R M)}
    (hp : letI := dual R H M; letI := ComoduleAlgebra.symmetricAlgebra R H (Module.Dual R M)
      p ∈ ComoduleAlgebra.coinvariants R H (SymmetricAlgebra R (Module.Dual R M))) :
    SymmetricAlgebra.lift (Module.Dual.eval R M (basePointsRepresentation M g m)) p =
      SymmetricAlgebra.lift (Module.Dual.eval R M m) p := by
  have h := congrArg g.ofConv (orbitCoordinates_eq_algebraMap_of_mem_coinvariants (H := H) m hp)
  rw [← AlgHom.comp_apply, comp_orbitCoordinates, g.ofConv.commutes] at h
  exact h

end Ring

section Field

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

omit [Module.Finite k M] in
private theorem map_fst_dualMap_mem_homogeneousSubmodule {d : ℕ}
    {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : p ∈ SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M) d) :
    SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap p ∈
      SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)) d := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul x hx i y _ ihy =>
    obtain ⟨φ, rfl⟩ := hx
    rw [map_mul, SymmetricAlgebra.map_apply_ι, Nat.succ_eq_add_one, add_comm]
    exact SetLike.mul_mem_graded (SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _) ihy

omit [Module.Finite k M] in
private theorem orbitCoordinates_mk_one_comp_map_fst (v : M) :
    (orbitCoordinates (H := H) ((v, 1) : M × k)).comp
        (SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap) =
      orbitCoordinates (H := H) v := by
  ext φ
  have hφ : (LinearMap.fst k M k).dualMap φ ∘ₗ LinearMap.inl k M k = φ := by
    ext x
    simp
  simp [matrixCoefficient_prodTrivial, hφ]

omit [Module.Finite k M] in
private theorem lift_eval_mk_one_comp_map_fst (w : M) :
    (SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (w, 1))).comp
        (SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap) =
      SymmetricAlgebra.lift (Module.Dual.eval k M w) := by
  ext φ
  simp

/-- **Invariant polynomial functions are constant on orbit closures.** Over any field `k`, if the
point `(w, 1)` lies in the closure of the projective orbit image of `(v, 1)`, then every
`G`-invariant polynomial function in `Sym(M*)^G` takes the same value at `w` and `v`. Neither
algebraic closedness nor finite generation of `H` is needed. -/
theorem lift_eval_eq_of_mem_closure_projectiveOrbitMap {v w : M}
    (hw : projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))))
    {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : letI := dual k H M; letI := ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k M)
      p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M))) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) p =
      SymmetricAlgebra.lift (Module.Dual.eval k M v) p := by
  classical
  let _ := dual k H M
  let _ := ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k M)
  let 𝒜 := SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)
  -- Reduce to homogeneous coinvariants via the graded decomposition of `Sym(M*)`.
  suffices ∀ (d : ℕ) (s : SymmetricAlgebra k (Module.Dual k M)),
      s ∈ 𝒜 d →
      s ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M)) →
      SymmetricAlgebra.lift (Module.Dual.eval k M w) s =
        SymmetricAlgebra.lift (Module.Dual.eval k M v) s by
    rw [← DirectSum.sum_support_decompose 𝒜 p, map_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ this d _ (SetLike.coe_mem _)
      (ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra hp d)
  intro d s hs hsinv
  rcases d with _ | d
  · obtain ⟨r, rfl⟩ : ∃ r : k, algebraMap k (SymmetricAlgebra k (Module.Dual k M)) r = s :=
      ⟨SymmetricAlgebra.homogeneousSubmoduleZeroEquiv k (Module.Dual k M) ⟨s, hs⟩,
        SymmetricAlgebra.algebraMap_homogeneousSubmoduleZeroEquiv_apply _ _ _⟩
    simp
  · -- Homogenize `s - s(v)` to degree `d + 1` in `Sym((M × k)*)` using the trivial coordinate `t`.
    set c : k := SymmetricAlgebra.lift (Module.Dual.eval k M v) s
    let t : SymmetricAlgebra k (Module.Dual k (M × k)) :=
      SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)
    let q : SymmetricAlgebra k (Module.Dual k (M × k)) :=
      SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap s - c • t ^ (d + 1)
    have hq_hom : q ∈ SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)) (d + 1) := by
      refine sub_mem (map_fst_dualMap_mem_homogeneousSubmodule hs) (Submodule.smul_mem _ _ ?_)
      have ht : t ∈ SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)) 1 :=
        SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _
      simpa using SetLike.pow_mem_graded (d + 1) ht
    have hq_orbit : orbitCoordinates (H := H) ((v, 1) : M × k) q = 0 := by
      have ht_orb : orbitCoordinates (H := H) ((v, 1) : M × k) t = 1 := by
        simp [t, matrixCoefficient_prodTrivial]
      simp only [q, map_sub, map_smul, map_pow, ht_orb, one_pow,
        ← AlgHom.comp_apply, orbitCoordinates_mk_one_comp_map_fst]
      rw [orbitCoordinates_eq_algebraMap_of_mem_coinvariants v hsinv, Algebra.smul_def, mul_one,
        sub_self]
    let V : (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))).Opens :=
      Proj.basicOpen _ q
    have hpre : projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v) ⁻¹ᵁ
        V = ⊥ := by
      rw [projectiveOrbitMap_preimage_basicOpen _ _ (Nat.succ_pos d) hq_hom, hq_orbit, map_zero,
        Scheme.basicOpen_zero]
    have hrange : Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)) ⊆ (V : Set _)ᶜ := by
      rintro _ ⟨x, rfl⟩ hx
      have hx' : x ∈ projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v) ⁻¹ᵁ V :=
        (Scheme.Hom.mem_preimage _).mpr hx
      rw [hpre] at hx'
      exact hx'
    have hw_not_mem : projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∉ (V : Set _) :=
      closure_minimal hrange V.isOpen.isClosed_compl hw
    have hq_mem : q ∈ (projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))).asHomogeneousIdeal := by
      by_contra h
      exact hw_not_mem h
    have hmem := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((w, 1) : M × k)
      (Module.isUnimodular_mk_one w) 1 hq_hom).mp
        (by simpa [AlgHom.convOne_def] using hq_mem)
    simp only [map_one, one_apply_eq_self] at hmem
    have ht_eval : SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (w, 1)) t = 1 := by
      simp [t]
    simp only [q, map_sub, map_smul, map_pow, ht_eval, one_pow, smul_eq_mul, mul_one,
      ← AlgHom.comp_apply, lift_eval_mk_one_comp_map_fst] at hmem
    exact sub_eq_zero.mp hmem

/-- **Conical orbits contain zero in their closure.** Over an infinite field `k`, if the rational
orbit of `v` contains every nonzero scalar multiple `t • v`, then the line through `(0, 1)` lies in
the closure of the projective orbit image of `(v, 1)`. Neither algebraic closedness nor finite
generation of `H` is needed. -/
theorem mem_closure_projectiveOrbitMap_zero_of_forall_smul [Infinite k] {v : M}
    (hv : ∀ t : k, t ≠ 0 →
      ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = t • v) :
    projectiveOrbitMap (H := H) ((0, 1) : M × k) (Module.isUnimodular_mk_one (0 : M))
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))) := by
  classical
  let 𝒜 := SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  rw [mem_closure_iff]
  intro U hU h0U
  obtain ⟨_, ⟨f, rfl⟩, h0f, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open h0U hU
  let x₀ : ProjectiveSpectrum 𝒜 :=
    projectiveOrbitMap (H := H) ((0, 1) : M × k) (Module.isUnimodular_mk_one (0 : M))
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))
  have hproj : ∃ d : ℕ, x₀ ∈ ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 d f) := by
    have h0f' : x₀ ∈ ⨆ i : ℕ, ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 i f) := by
      rw [← ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 f]
      exact h0f
    exact TopologicalSpace.Opens.mem_iSup.mp h0f'
  obtain ⟨d, h0q⟩ := hproj
  set q := GradedRing.proj 𝒜 d f
  have hq_hom : q ∈ 𝒜 d := SetLike.coe_mem _
  have hq_le : ProjectiveSpectrum.basicOpen 𝒜 q ≤ ProjectiveSpectrum.basicOpen 𝒜 f := by
    rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 f]
    exact le_iSup (fun i ↦ ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 i f)) d
  let L : Module.Dual k (M × k) →ₗ[k] Polynomial k :=
    { toFun := fun φ ↦ Polynomial.C (φ (0, 1)) + Polynomial.X * Polynomial.C (φ (v, 0))
      map_add' := fun φ ψ ↦ by
        simp only [LinearMap.add_apply, map_add, mul_add]
        ring
      map_smul' := fun r φ ↦ by
        simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul,
          Polynomial.smul_eq_C_mul]
        ring }
  let P : Polynomial k := SymmetricAlgebra.lift L q
  have hPeval (t : k) :
      P.eval t = SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1)) q := by
    have hcomp : (Polynomial.aeval t).comp (SymmetricAlgebra.lift L) =
        SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1)) := by
      ext φ
      change Polynomial.aeval t
          (SymmetricAlgebra.lift L (SymmetricAlgebra.ι k (Module.Dual k (M × k)) φ)) =
        SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) φ)
      rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply]
      have hdecomp : (t • v, (1 : k)) = (0, (1 : k)) + t • (v, (0 : k)) := by
        ext <;> simp
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Module.Dual.eval_apply]
      rw [hdecomp, map_add, map_smul, smul_eq_mul]
    have hq := congrArg (fun g ↦ g q) hcomp
    simpa only [AlgHom.comp_apply, P, Polynomial.coe_aeval_eq_eval] using hq
  have hP0 : P.eval 0 ≠ 0 := by
    rw [hPeval 0, zero_smul]
    intro hzero
    apply (ProjectiveSpectrum.mem_basicOpen 𝒜 q _).mp h0q
    have hmem := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((0, 1) : M × k)
      (Module.isUnimodular_mk_one (0 : M)) 1 hq_hom).mpr (by simpa using hzero)
    simpa [AlgHom.convOne_def] using hmem
  have hPne : P ≠ 0 := fun h ↦ hP0 (by simp [h])
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert (0 : k) P.roots.toFinset)
  have ht0 : t ≠ 0 := fun h ↦ ht (Finset.mem_insert.mpr (Or.inl h))
  have hPt : P.eval t ≠ 0 := by
    intro hzero
    exact ht (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hPne).mpr hzero)))
  obtain ⟨g, hg⟩ := hv t ht0
  refine ⟨projectiveOrbitMap (H := H) ((t • v, 1) : M × k) (Module.isUnimodular_mk_one (t • v))
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)), hfU (hq_le ?_), ?_⟩
  · intro hmem
    apply hPt
    rw [hPeval t]
    have h := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((t • v, 1) : M × k)
      (Module.isUnimodular_mk_one (t • v)) 1 hq_hom).mp (by simpa [AlgHom.convOne_def] using hmem)
    simpa using h
  · rw [← range_projectiveOrbitMap_mk_one_basePointsRepresentation g v, hg]
    exact Set.mem_range_self _

end Field

end Invariants

namespace VectorOrbit

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Orbits are determined by their images.** Two vectors have the same geometric orbit image
in `P(M × k)` exactly when they are rationally conjugate. -/
theorem image_injective : Function.Injective (image : VectorOrbit k H M → Set _) := by
  intro O O' h
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  rw [image_mk, image_mk, eq_comm, range_projectiveOrbitMap_eq_iff] at h
  obtain ⟨g, hg⟩ := exists_span_basePointsRepresentation_eq_of_mem_range _ _ _ _ h
  exact mk_eq_mk_iff.mpr ⟨g, basePointsRepresentation_eq_of_span_eq hg⟩

/-- **Orbits are determined by their closures.** Two rational orbits whose geometric images
have the same closure in `P(M × k)` are equal. -/
theorem closure_image_injective :
    Function.Injective fun O : VectorOrbit k H M ↦ closure O.image := by
  intro O O' h
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  simp only [image_mk] at h
  refine image_injective ?_
  rw [image_mk, image_mk]
  refine (range_projectiveOrbitMap_eq_of_mem_closure_of_mem_closure _ _ ?_ ?_).symm
  · exact h ▸ subset_closure (Set.mem_range_self _)
  · exact h.symm ▸ subset_closure (Set.mem_range_self _)

/-- The **closure order** on rational orbits: `O ≤ O'` when `O` lies in the closure of `O'`.
Equivalently, the closure of `O` lies in the closure of `O'`. -/
noncomputable instance instPartialOrder : PartialOrder (VectorOrbit k H M) :=
  PartialOrder.lift _ closure_image_injective

/-- In the closure order, `O ≤ O'` exactly when the closure of `O` lies in that of `O'`. -/
theorem le_iff_closure_image_subset {O O' : VectorOrbit k H M} :
    O ≤ O' ↔ closure O.image ⊆ closure O'.image :=
  Iff.rfl

/-- In the closure order, `O ≤ O'` exactly when `O` lies in the closure of `O'`. -/
theorem le_iff_image_subset_closure {O O' : VectorOrbit k H M} :
    O ≤ O' ↔ O.image ⊆ closure O'.image :=
  isClosed_closure.closure_subset_iff

/-- The orbit of `w` lies below the orbit of `v` exactly when the line through `(w, 1)` lies in
the closure of the orbit of `v`. -/
theorem mk_le_mk_iff {v w : M} :
    (mk w : VectorOrbit k H M) ≤ mk v ↔
      projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v))) := by
  rw [le_iff_image_subset_closure, image_mk, image_mk]
  exact range_projectiveOrbitMap_subset_closure_iff _ _ _ _

/-- The orbit of `w` lies strictly below the orbit of `v` exactly when the line through `(w, 1)`
lies in the boundary of the orbit of `v`. -/
theorem mk_lt_mk_iff {v w : M} :
    (mk w : VectorOrbit k H M) < mk v ↔
      projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v))) \
          Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
            (Module.isUnimodular_mk_one v)) := by
  rw [lt_iff_le_and_ne, mk_le_mk_iff, Ne, ← image_injective.eq_iff, image_mk, image_mk,
    range_projectiveOrbitMap_eq_iff, Set.mem_sdiff]

/-- **Strictly smaller orbits have strictly smaller dimension.** -/
theorem strictMono_topologicalKrullDim_image :
    StrictMono fun O : VectorOrbit k H M ↦ topologicalKrullDim O.image := by
  intro O O' h
  induction O using VectorOrbit.ind with | h w
  induction O' using VectorOrbit.ind with | h v
  beta_reduce
  rw [image_mk, image_mk]
  exact Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt _ _ (mk_lt_mk_iff.mp h)

/-- **Invariant polynomial functions are constant on closure order intervals.** If `mk w ≤ mk v`
in the closure order, then every `G`-invariant polynomial function takes the same value at `w`
and `v`. -/
theorem lift_eval_eq_of_le {v w : M} (hle : (mk w : VectorOrbit k H M) ≤ mk v)
    {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : letI := dual k H M; letI := ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k M)
      p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M))) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) p =
      SymmetricAlgebra.lift (Module.Dual.eval k M v) p :=
  lift_eval_eq_of_mem_closure_projectiveOrbitMap (mk_le_mk_iff.mp hle) hp

/-- **Conical orbits lie above zero in the closure order.** If the rational orbit of `v` contains
every nonzero scalar multiple of `v`, then `mk 0 ≤ mk v`. -/
theorem mk_zero_le_mk_of_forall_smul {v : M}
    (hv : ∀ t : k, t ≠ 0 →
      ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = t • v) :
    (mk (0 : M) : VectorOrbit k H M) ≤ mk v :=
  mk_le_mk_iff.mpr (mem_closure_projectiveOrbitMap_zero_of_forall_smul hv)

omit [Algebra.FiniteType k H] in
private theorem exists_mk_one_eq_of_mem_basicOpen_snd_inter_closedPoints
    {x : Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))}
    (hxU : x ∈ (Proj.basicOpen
      (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
      (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _))
    (hxc : x ∈ closedPoints _) :
    ∃ w : M, projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) = x := by
  obtain ⟨⟨v, c⟩, hm, rfl⟩ :=
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) x).mp hxc
  have hc : c ≠ 0 := by
    intro hc0
    apply hxU
    have h := (ι_mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((v, c) : M × k) hm 1
      (LinearMap.snd k M k)).mpr (by simp [hc0])
    simpa [AlgHom.convOne_def] using h
  refine ⟨c⁻¹ • v, ?_⟩
  have hspan : k ∙ ((c⁻¹ • v, 1) : M × k) = k ∙ ((v, c) : M × k) := by
    have hsmul : c⁻¹ • ((v, c) : M × k) = (c⁻¹ • v, 1) := by
      ext <;> simp [hc]
    rw [← hsmul]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)) _
  have h := (projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H)
    ((c⁻¹ • v, 1) : M × k) (Module.isUnimodular_mk_one (c⁻¹ • v))
    ((v, c) : M × k) hm 1 1).mpr (by simpa using hspan)
  simpa [AlgHom.convOne_def] using h

omit [IsAlgClosed k] in
private theorem isConstructible_image (O : VectorOrbit k H M) :
    Topology.IsConstructible O.image := by
  induction O using VectorOrbit.ind with | h v
  rw [image_mk]
  exact isConstructible_range_projectiveOrbitMap (H := H) ((v, 1) : M × k)
    (Module.isUnimodular_mk_one v)

/-- **Closure decomposition for orbits with finite lower set.** When only finitely many rational
orbits lie below `O` in the closure order, the closure of `O` inside the affine chart `M = {t ≠ 0}`
of `P(M × k)` is the exact union of the full scheme-point orbit images `O' ≤ O`. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion_le {O : VectorOrbit k H M}
    (hfin : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    closure O.image ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image := by
  let U : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))) :=
    (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
      (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _)
  have hU_c : Topology.IsConstructible U :=
    (NoetherianSpace.isCompact U).isConstructible (Proj.basicOpen _ _).isOpen
  have hcl_c : Topology.IsConstructible (closure O.image) :=
    ((NoetherianSpace.isCompact (closure O.image)ᶜ).isConstructible
      isClosed_closure.isOpen_compl).of_compl
  have hUnion_c : Topology.IsConstructible
      (⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image) :=
    Topology.IsConstructible.biUnion hfin fun O' _ ↦ isConstructible_image O'
  rw [(hcl_c.inter hU_c).eq_iff_inter_closedPoints_eq hUnion_c]
  induction O using VectorOrbit.ind with | h v
  ext x
  constructor
  · rintro ⟨⟨hxcl, hxU⟩, hxc⟩
    obtain ⟨w, rfl⟩ := exists_mk_one_eq_of_mem_basicOpen_snd_inter_closedPoints (H := H) hxU hxc
    rw [image_mk] at hxcl
    exact ⟨Set.mem_biUnion (mk_le_mk_iff.mpr hxcl)
      ((image_mk (k := k) (H := H) w).symm ▸ Set.mem_range_self _), hxc⟩
  · rintro ⟨hx, hxc⟩
    obtain ⟨O', hO'le, hxO'⟩ := Set.mem_iUnion₂.mp hx
    have hxU : x ∈ U := by
      induction O' using VectorOrbit.ind with | h u
      rw [image_mk] at hxO'
      exact range_projectiveOrbitMap_subset_basicOpen_snd u hxO'
    exact ⟨⟨(le_iff_image_subset_closure.mp hO'le) hxO', hxU⟩, hxc⟩

/-- **Boundary decomposition for orbits with finite lower set.** When only finitely many rational
orbits lie below `O` in the closure order, the boundary `closure O \ O` inside the affine chart
`M = {t ≠ 0}` of `P(M × k)` is the exact union of the full scheme-point orbit images `O' < O`. -/
theorem closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt {O : VectorOrbit k H M}
    (hfin : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' < O}, O'.image := by
  let U : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))) :=
    (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
      (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _)
  have hfin_lt : {O' : VectorOrbit k H M | O' < O}.Finite :=
    hfin.subset fun _ (h : _ < O) ↦ le_of_lt h
  have hU_c : Topology.IsConstructible U :=
    (NoetherianSpace.isCompact U).isConstructible (Proj.basicOpen _ _).isOpen
  have hcl_c : Topology.IsConstructible (closure O.image) :=
    ((NoetherianSpace.isCompact (closure O.image)ᶜ).isConstructible
      isClosed_closure.isOpen_compl).of_compl
  have hUnion_c : Topology.IsConstructible
      (⋃ O' ∈ {O' : VectorOrbit k H M | O' < O}, O'.image) :=
    Topology.IsConstructible.biUnion hfin_lt fun O' _ ↦ isConstructible_image O'
  rw [((hcl_c.sdiff (isConstructible_image O)).inter hU_c).eq_iff_inter_closedPoints_eq hUnion_c]
  induction O using VectorOrbit.ind with | h v
  ext x
  constructor
  · rintro ⟨⟨hxbd, hxU⟩, hxc⟩
    obtain ⟨w, rfl⟩ := exists_mk_one_eq_of_mem_basicOpen_snd_inter_closedPoints (H := H) hxU hxc
    rw [image_mk] at hxbd
    exact ⟨Set.mem_biUnion (mk_lt_mk_iff.mpr hxbd)
      ((image_mk (k := k) (H := H) w).symm ▸ Set.mem_range_self _), hxc⟩
  · rintro ⟨hx, hxc⟩
    obtain ⟨O', hO'lt, hxO'⟩ := Set.mem_iUnion₂.mp hx
    have hxU : x ∈ U := by
      induction O' using VectorOrbit.ind with | h u
      rw [image_mk] at hxO'
      exact range_projectiveOrbitMap_subset_basicOpen_snd u hxO'
    refine ⟨⟨⟨(le_iff_image_subset_closure.mp (le_of_lt hO'lt)) hxO', ?_⟩, hxU⟩, hxc⟩
    intro hxO
    obtain ⟨w, rfl⟩ := exists_mk_one_eq_of_mem_basicOpen_snd_inter_closedPoints (H := H) hxU hxc
    induction O' using VectorOrbit.ind with | h u
    rw [image_mk] at hxO' hxO
    have hwu : (mk w : VectorOrbit k H M) = mk u := image_injective <| by
      rw [image_mk, image_mk]
      exact (range_projectiveOrbitMap_eq_iff _ _ _ _).mpr hxO'
    have hwv : (mk w : VectorOrbit k H M) = mk v := image_injective <| by
      rw [image_mk, image_mk]
      exact (range_projectiveOrbitMap_eq_iff _ _ _ _).mpr hxO
    exact hO'lt.ne (hwu.symm.trans hwv)

end VectorOrbit

end TauCeti.Comodule
