/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.Data.List.Involutive

/-!
# Corestriction of subcomodules

Corestriction of a comodule along a coalgebra morphism preserves every subcomodule and its
underlying submodule. When the coalgebra morphism is an equivalence, this gives an order
isomorphism between the subcomodule lattices before and after corestriction.

This is Layer 1 infrastructure for the reductive-groups roadmap: changing coordinate
coalgebras must preserve the invariant subspaces of their comodules.

## Main declarations

* `TauCeti.Subcomodule.corestrict`: corestrict a subcomodule along a coalgebra morphism.
* `TauCeti.Subcomodule.corestrictSymm`: recover a subcomodule before corestriction along a
  coalgebra equivalence.
* `TauCeti.Subcomodule.corestrictOrderIso`: the carrier-preserving order isomorphism induced
  by a coalgebra equivalence.
* `TauCeti.Subcomodule.isSimpleOrder_of_corestrict_eq_ofWeights`: distinct one-dimensional
  weights connected by subcomodule-preserving involutions give a simple comodule.
* `TauCeti.Subcomodule.single_smul_mem_of_corestrict_eq_ofWeights`: restriction to distinct
  one-dimensional weights extracts each scaled coordinate vector of a subcomodule vector.
* `TauCeti.Subcomodule.ofCorestrictOfSplit` and `corestrictOrderIsoOfSplit`: recovery and
  order correspondence given a linear retraction over a commutative semiring.
* `TauCeti.Subcomodule.map_id_coact_coe_eq_tmul_one`: a vector of a subcomodule fixed by the
  corestricted coaction is fixed by the corestricted coaction of the ambient comodule.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Subcomodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Corestriction along a coalgebra morphism preserves a subcomodule and its carrier. -/
def corestrict (f : C →ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict f
    Subcomodule R D M :=
  letI : Comodule R D M := Comodule.Corestrict f
  Subcomodule.ofSubmodule W.carrier fun m hm ↦ by
    obtain ⟨t, ht⟩ := W.coact_mem hm
    refine ⟨TensorProduct.map LinearMap.id f.toLinearMap t, ?_⟩
    rw [Comodule.corestrict_coact_apply]
    calc
      _ = TensorProduct.map LinearMap.id f.toLinearMap
          (TensorProduct.map W.carrier.subtype LinearMap.id t) := by
            simp [TensorProduct.map_map]
      _ = _ := congrArg (TensorProduct.map LinearMap.id f.toLinearMap) ht

/-- Corestriction of a subcomodule does not change its underlying submodule. -/
@[simp]
theorem corestrict_toSubmodule (f : C →ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict f
    (W.corestrict f).toSubmodule = W.toSubmodule :=
  (rfl)

/-- Membership is unchanged by corestriction of a subcomodule. -/
@[simp]
theorem mem_corestrict (f : C →ₗc[R] D) (W : Subcomodule R C M) (m : M) :
    letI : Comodule R D M := Comodule.Corestrict f
    m ∈ W.corestrict f ↔ m ∈ W :=
  Iff.rfl

private theorem corestrict_symm_instance_eq (e : C ≃ₗc[R] D) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    Comodule.Corestrict e.symm.toCoalgHom = (inferInstance : Comodule R C M) := by
  let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  apply Comodule.ext
  -- `Comodule.ext` presents the goal through the inferred instance projection. Unfolding that
  -- projection is necessary to expose the named corestriction coaction lemmas used below.
  change Comodule.corestrictCoact e.symm.toCoalgHom = Comodule.coact
  rw [← Comodule.corestrictCoact_comp e.toCoalgHom e.symm.toCoalgHom]
  have hcomp : e.symm.toCoalgHom.comp e.toCoalgHom = CoalgHom.id R C := by
    ext c
    simp
  rw [hcomp, Comodule.corestrictCoact_id]

/-- Pull a subcomodule of a corestricted comodule back along a coalgebra equivalence. -/
def corestrictSymm (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) : Subcomodule R C M :=
  let instOriginal : Comodule R C M := inferInstance
  letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  let instDouble : Comodule R C M := Comodule.Corestrict e.symm.toCoalgHom
  let W' : @Subcomodule R C M _ _ _ _ _ _ instDouble := by
    letI : Comodule R C M := instDouble
    exact W.corestrict e.symm.toCoalgHom
  have h : instDouble = instOriginal := by
    let _ : Comodule R C M := instOriginal
    exact corestrict_symm_instance_eq e
  letI : Comodule R C M := instOriginal
  Subcomodule.ofSubmodule W.carrier fun m hm => by
    have hmem : instDouble.coact m ∈ LinearMap.range
        (TensorProduct.map W.carrier.subtype (LinearMap.id : C →ₗ[R] C)) := by
      let _ : Comodule R C M := instDouble
      have hmem' := W'.coact_mem hm
      -- The source of `hmem'` contains `W'.carrier`, while the target contains `W.carrier`.
      -- These subcomodules have different dependent comodule-instance indices, so expose the
      -- carrier equality explicitly before rewriting it with the corestriction API.
      rw [show W'.carrier = W.carrier by
        exact corestrict_toSubmodule e.symm.toCoalgHom W] at hmem'
      exact hmem'
    rw [congrArg (fun rho : Comodule R C M => rho.coact) h] at hmem
    exact hmem

/-- Pulling a subcomodule back from a corestriction preserves its underlying submodule. -/
@[simp]
theorem corestrictSymm_toSubmodule (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    (corestrictSymm e W).toSubmodule = W.toSubmodule :=
  by
    ext m
    rfl

/-- Membership is unchanged when pulling a subcomodule back from a corestriction. -/
@[simp]
theorem mem_corestrictSymm (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) (m : M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    m ∈ corestrictSymm e W ↔ m ∈ W :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    -- Membership notation hides the underlying submodules behind subcomodules indexed by
    -- dependent comodule instances; expose those carriers so the preservation lemma can rewrite.
    change m ∈ (corestrictSymm e W).toSubmodule ↔ m ∈ W.toSubmodule
    rw [corestrictSymm_toSubmodule]

/-- A coalgebra equivalence identifies the subcomodules of a comodule with those of its
corestriction, without changing their underlying submodules. -/
def corestrictOrderIso (e : C ≃ₗc[R] D) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    Subcomodule R C M ≃o Subcomodule R D M :=
  letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  { toFun := fun W ↦ W.corestrict e.toCoalgHom
    invFun := corestrictSymm e
    -- Both directions are built with `ofSubmodule W.carrier`, so carrier equality and order
    -- reflection hold definitionally.
    left_inv := by
      intro W
      ext m
      rfl
    right_inv := by
      intro W
      ext m
      rfl
    map_rel_iff' := by
      rfl }

/-- The forward order correspondence is corestriction. -/
@[simp]
theorem corestrictOrderIso_apply (e : C ≃ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    corestrictOrderIso e W = W.corestrict e.toCoalgHom :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    ext m
    rfl

/-- The inverse order correspondence is pullback from the corestriction. -/
@[simp]
theorem corestrictOrderIso_symm_apply (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    (corestrictOrderIso e).symm W = corestrictSymm e W :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    ext m
    rfl

section WeightGraph

variable {H : Type v} [AddCommGroup H]
variable {G : Type w} {I : Type x} [Finite I] [DecidableEq I]

section CommRing

variable {k : Type u} [CommRing k] [Module k H] [Coalgebra k H]
variable [Comodule k H (I → k)]

/-- Restriction to distinct one-dimensional weights extracts every scaled coordinate vector of a
vector in a subcomodule. -/
theorem single_smul_mem_of_corestrict_eq_ofWeights
    (f : H →ₗc[k] MonoidAlgebra k G) (wt : I → G) (hwt : Function.Injective wt)
    (hcomodule :
      Comodule.Corestrict f = Comodule.ofWeights (Pi.basisFun k I) wt)
    (N : Subcomodule k H (I → k)) {v : I → k} (hv : v ∈ N) (a : I) :
    v a • Pi.single a 1 ∈ N := by
  let _ : Comodule k (MonoidAlgebra k G) (I → k) := Comodule.Corestrict f
  have hvweight : v ∈ N.corestrict f :=
    (mem_corestrict f N v).2 hv
  have hp := Comodule.weightProj_mem_subcomodule (N.corestrict f) (wt a) hvweight
  have hpN :
      Comodule.weightProj k G (I → k) (wt a) v ∈ N :=
    (mem_corestrict f N _).1 hp
  have hproj :
      (let _ : Comodule k (MonoidAlgebra k G) (I → k) := Comodule.Corestrict f;
        Comodule.weightProj k G (I → k) (wt a) v) =
      (let _ : Comodule k (MonoidAlgebra k G) (I → k) :=
          Comodule.ofWeights (Pi.basisFun k I) wt;
        Comodule.weightProj k G (I → k) (wt a) v) :=
    -- `weightProj` is selected through the comodule instance, so transport that instance
    -- explicitly across `hcomodule` before using its closed formula for `ofWeights`.
    congrArg (fun c : Comodule k (MonoidAlgebra k G) (I → k) ↦
      let _ := c;
      Comodule.weightProj k G (I → k) (wt a) v) hcomodule
  rw [hproj, Comodule.weightProj_ofWeights_eq (Pi.basisFun k I) wt hwt] at hpN
  simpa only [Pi.basisFun_repr, Finsupp.single_eq_same, Pi.basisFun_apply,
    Pi.single_smul', smul_eq_mul, mul_one] using hpN

end CommRing

section Field

variable {k : Type u} [Field k] [Module k H] [Coalgebra k H]
variable [Comodule k H (I → k)]

/-- **A comodule with distinct one-dimensional weights and a connected weight graph is
simple.** The graph edges are supplied as involutions of the basis indices which preserve
membership of basis vectors in every subcomodule. This isolates the type-independent argument
used for minuscule standard comodules: restriction to the torus extracts a coordinate, and
connected root moves propagate that coordinate basis vector to the whole basis. -/
theorem isSimpleOrder_of_corestrict_eq_ofWeights
    (f : H →ₗc[k] MonoidAlgebra k G) (wt : I → G) (hwt : Function.Injective wt)
    (hcomodule : Comodule.Corestrict f = Comodule.ofWeights (Pi.basisFun k I) wt)
    {J : Type*} (reflect : J → I → I)
    (hinvolutive : ∀ j, Function.Involutive (reflect j))
    (hreflect : ∀ (N : Subcomodule k H (I → k)) a j,
      Pi.single a 1 ∈ N → Pi.single (reflect j a) 1 ∈ N)
    (base : I)
    (hconnected : ∀ a, ∃ l : List J, l.foldl (fun b j ↦ reflect j b) base = a) :
    IsSimpleOrder (Subcomodule k H (I → k)) := by
  classical
  let _ := Fintype.ofFinite I
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have hone : (Pi.single base (1 : k) : I → k) ∈
        (⊥ : Subcomodule k H (I → k)) := h ▸ Subcomodule.mem_top _
    rw [Subcomodule.mem_bot] at hone
    simpa using congrFun hone base
  · intro N
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      obtain ⟨v, hv, hv0⟩ := N.ne_bot_iff.mp hN
      obtain ⟨b, hb⟩ := Function.ne_iff.mp hv0
      have hb0 : v b ≠ 0 := by simpa using hb
      have hbmem := single_smul_mem_of_corestrict_eq_ofWeights f wt hwt hcomodule N hv b
      have hseed : Pi.single b 1 ∈ N := by
        have hscaled := N.toSubmodule.smul_mem (v b)⁻¹ hbmem
        rw [← Subcomodule.mem_toSubmodule]
        simpa only [inv_smul_smul₀ hb0] using hscaled
      obtain ⟨l, hl⟩ := hconnected b
      have hbase : Pi.single base 1 ∈ N := by
        apply (predicate_foldl_iff_of_involutive
          (fun a ↦ Pi.single a 1 ∈ N) reflect hinvolutive (hreflect N) l base).mp
        rwa [hl]
      apply top_unique
      intro v _
      rw [← (Pi.basisFun k I).sum_repr v]
      exact N.toSubmodule.sum_mem fun a _ ↦ N.toSubmodule.smul_mem _ (by
        have ha := (predicate_foldl_iff_of_involutive
          (fun a ↦ Pi.single a 1 ∈ N) reflect hinvolutive (hreflect N)
          (hconnected a).choose base).mpr hbase
        rw [(hconnected a).choose_spec] at ha
        rw [Subcomodule.mem_toSubmodule]
        simpa only [Pi.basisFun_apply] using ha)

end Field

end WeightGraph

section Induced

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D] [One D]
variable {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A vector of a subcomodule that the corestricted coaction fixes is fixed by the corestricted
coaction of the ambient comodule.

This is the corestricted analogue of `TauCeti.Subcomodule.coact_coe_eq_tmul_one`; the coalgebra
morphism is spelled out rather than installed as a comodule instance, so that both sides read in
the ambient coalgebra `C`. -/
theorem map_id_coact_coe_eq_tmul_one (f : C →ₗc[R] D) (W : Subcomodule R C M) {n : W}
    (hn : TensorProduct.map LinearMap.id f.toLinearMap
        (Comodule.coact (R := R) (C := C) (M := W) n) = n ⊗ₜ[R] (1 : D)) :
    TensorProduct.map LinearMap.id f.toLinearMap
        (Comodule.coact (R := R) (C := C) (M := M) (n : M)) = (n : M) ⊗ₜ[R] (1 : D) := by
  have h := congrArg
    (TensorProduct.map (SMulMemClass.subtype W) (LinearMap.id : D →ₗ[R] D)) hn
  rw [TensorProduct.map_tmul, SMulMemClass.subtype_apply, LinearMap.id_coe, id_eq] at h
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id] at h
  -- The explicit factorization aligns the subtype coaction with the ambient tensor map;
  -- elaboration cannot infer the intermediate tensor factors from the surrounding rewrite.
  rw [show TensorProduct.map (SMulMemClass.subtype W) f.toLinearMap =
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) f.toLinearMap).comp
        (TensorProduct.map (SMulMemClass.subtype W) (LinearMap.id : C →ₗ[R] C)) by
    rw [← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id],
    LinearMap.comp_apply, ← LinearMap.rTensor_def, Subcomodule.subtype_rTensor_coact] at h
  exact h

end Induced

section Split

variable {k : Type u} [CommSemiring k]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]
variable {V : Type x} [AddCommMonoid V] [Module k V] [Comodule k C V]

/-- A linear retraction of a coalgebra morphism recovers every subcomodule of the
corestricted comodule, with the same underlying submodule. -/
def ofCorestrictOfSplit (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id)
    (W : letI : Comodule k D V := Comodule.Corestrict f
      Subcomodule k D V) : Subcomodule k C V :=
  letI : Comodule k D V := Comodule.Corestrict f
  Subcomodule.ofSubmodule W.carrier (fun m hm ↦ by
    obtain ⟨t, ht⟩ := W.coact_mem hm
    refine ⟨TensorProduct.map LinearMap.id r t, ?_⟩
    have h := congrArg (TensorProduct.map (LinearMap.id : V →ₗ[k] V) r) ht
    simpa only [Comodule.corestrict_coact_apply, TensorProduct.map_map,
      LinearMap.id_comp, LinearMap.comp_id, hr, TensorProduct.map_id,
      LinearMap.id_apply] using h)

/-- Recovery from a split corestriction preserves the underlying submodule. -/
@[simp]
theorem ofCorestrictOfSplit_toSubmodule (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id)
    (W : letI : Comodule k D V := Comodule.Corestrict f
      Subcomodule k D V) :
    letI : Comodule k D V := Comodule.Corestrict f
    (ofCorestrictOfSplit f r hr W).toSubmodule = W.toSubmodule := by
  unfold ofCorestrictOfSplit
  exact Subcomodule.ofSubmodule_carrier _ _

/-- Membership is unchanged by recovery from a split corestriction. -/
@[simp]
theorem mem_ofCorestrictOfSplit (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id)
    (W : letI : Comodule k D V := Comodule.Corestrict f
      Subcomodule k D V) (m : V) :
    letI : Comodule k D V := Comodule.Corestrict f
    m ∈ ofCorestrictOfSplit f r hr W ↔ m ∈ W := by
  let _ : Comodule k D V := Comodule.Corestrict f
  rw [← mem_toSubmodule, ofCorestrictOfSplit_toSubmodule, mem_toSubmodule]

/-- Corestricting a subcomodule recovered through a linear retraction gives the original. -/
@[simp]
theorem corestrict_ofCorestrictOfSplit (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id)
    (W : letI : Comodule k D V := Comodule.Corestrict f
      Subcomodule k D V) :
    letI : Comodule k D V := Comodule.Corestrict f
    (ofCorestrictOfSplit f r hr W).corestrict f = W := by
  let _ : Comodule k D V := Comodule.Corestrict f
  ext m
  simp only [mem_corestrict, mem_ofCorestrictOfSplit]

/-- Recovering a corestricted subcomodule through a linear retraction gives the original. -/
@[simp]
theorem ofCorestrictOfSplit_corestrict (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id) (W : Subcomodule k C V) :
    ofCorestrictOfSplit f r hr (W.corestrict f) = W := by
  ext m
  simp only [mem_ofCorestrictOfSplit, mem_corestrict]

/-- The order isomorphism induced by a coalgebra morphism with a linear retraction
preserves underlying submodules. -/
def corestrictOrderIsoOfSplit (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id) :
    letI : Comodule k D V := Comodule.Corestrict f
    Subcomodule k C V ≃o Subcomodule k D V :=
  letI : Comodule k D V := Comodule.Corestrict f
  { toFun := fun W ↦ W.corestrict f
    invFun := ofCorestrictOfSplit f r hr
    left_inv := ofCorestrictOfSplit_corestrict f r hr
    right_inv := corestrict_ofCorestrictOfSplit f r hr
    map_rel_iff' := by
      rfl }

/-- The forward map of the split-corestriction order isomorphism is corestriction. -/
@[simp]
theorem corestrictOrderIsoOfSplit_apply (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id) (W : Subcomodule k C V) :
    corestrictOrderIsoOfSplit f r hr W = W.corestrict f := by
  let _ : Comodule k D V := Comodule.Corestrict f
  ext m
  rfl

/-- The inverse map of the split-corestriction order isomorphism recovers the subcomodule. -/
@[simp]
theorem corestrictOrderIsoOfSplit_symm_apply (f : C →ₗc[k] D) (r : D →ₗ[k] C)
    (hr : r.comp f.toLinearMap = LinearMap.id)
    (W : letI : Comodule k D V := Comodule.Corestrict f
      Subcomodule k D V) :
    letI : Comodule k D V := Comodule.Corestrict f
    (corestrictOrderIsoOfSplit f r hr).symm W = ofCorestrictOfSplit f r hr W := by
  let _ : Comodule k D V := Comodule.Corestrict f
  ext m
  rfl

end Split

end Subcomodule

end TauCeti
