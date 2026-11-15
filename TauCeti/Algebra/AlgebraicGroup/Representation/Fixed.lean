/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Fixed vectors and differentiation

For a connected affine group over an algebraically closed field of characteristic zero (or a
geometrically connected finite-type affine group over any field of characteristic zero),
a vector in a rational representation is fixed exactly when its differentiated action is
zero. More generally, a linear map intertwines rational representations exactly when it
intertwines their differentials, so a rational representation is determined on its underlying
vector space by its differentiated Lie-algebra action. Neither representation needs to be finite
dimensional.

The morphism criterion follows by applying the Lie-stable subspace criterion to the graph
of the linear map. Applying it to a map from the trivial representation gives the fixed
vector criterion. In particular this allows infinitesimal invariants, such as the center
of the tangent Lie algebra, to be recognized as rational invariants.

The graph argument uses
`Submodule.coact_mem_range_of_forall_differential_mem_of_geometricallyConnected`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open TauCeti
open scoped TensorProduct

universe u w x

namespace LinearMap

section GeometricallyConnected

variable {k : Type u} [Field k] [CharZero k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
  {N : Type x} [AddCommGroup N] [Module k N] [Comodule k H N]

/-- Over any field of characteristic zero, a linear map between representations of a geometrically
connected finite-type affine group is a rational representation morphism exactly when it
intertwines the differentiated actions. -/
theorem map_coact_iff_map_differential_of_geometricallyConnected
    (hH : geometricallyConnectedCommHopfAlgProperty k H) (f : M →ₗ[k] N) :
    TensorProduct.map f LinearMap.id ∘ₗ Comodule.coact (R := k) (C := H) =
        Comodule.coact (R := k) (C := H) ∘ₗ f ↔
      ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
        f (Comodule.differential (R := k) (H := H) d m) =
          Comodule.differential (R := k) (H := H) d (f m) := by
  refine ⟨fun hf ↦ Comodule.Hom.map_differential ⟨f, hf⟩, fun hf ↦ ?_⟩
  let : Comodule k H (M × N) := Comodule.Prod
  let q : M × N →ₗ[k] N := LinearMap.snd k M N - f.comp (LinearMap.fst k M N)
  have hq : q.comp f.graph.subtype = 0 := LinearMap.ext fun z ↦
    sub_eq_zero.mpr ((mem_graph_iff f z).mp z.2)
  ext m
  obtain ⟨t, ht⟩ := f.graph.coact_mem_range_of_forall_differential_mem_of_geometricallyConnected hH
    (fun d _ hz ↦ f.differential_mem_graph d (hf d) hz) ((mem_graph_iff f (m, f m)).mpr rfl)
  have hzero : q.rTensor H (Comodule.coact (R := k) (C := H) (m, f m)) = 0 := by
    simpa [← rTensor_def, ← rTensor_comp_apply, hq] using (congrArg (q.rTensor H) ht).symm
  suffices Comodule.coact (R := k) (C := H) (f m) -
      f.rTensor H (Comodule.coact (R := k) (C := H) m) = 0 from (sub_eq_zero.mp this).symm
  simpa [q, rTensor_sub, rTensor_comp_apply] using hzero

end GeometricallyConnected

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
variable {N : Type x} [AddCommGroup N] [Module k N] [Comodule k H N]

/-- For a connected affine group over an algebraically closed field of characteristic zero,
a linear map is a rational representation morphism exactly when it intertwines the
differentiated actions. -/
theorem map_coact_iff_map_differential (f : M →ₗ[k] N) :
    TensorProduct.map f LinearMap.id ∘ₗ Comodule.coact (R := k) (C := H) =
        Comodule.coact (R := k) (C := H) ∘ₗ f ↔
      ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
        f (Comodule.differential (R := k) (H := H) d m) =
          Comodule.differential (R := k) (H := H) d (f m) :=
  f.map_coact_iff_map_differential_of_geometricallyConnected
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr inferInstance)

end LinearMap

namespace TauCeti.Comodule

section GeometricallyConnected

variable {k : Type u} [Field k] [CharZero k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]

/-- Over any field of characteristic zero, two rational representation structures of a
geometrically connected finite-type affine group on the same vector space coincide if their
differentiated Lie-algebra actions agree. No finite-dimensionality assumption is needed. -/
theorem ext_of_differential_eq_of_geometricallyConnected
    (hH : geometricallyConnectedCommHopfAlgProperty k H) {M : Type w} [AddCommGroup M] [Module k M]
    {c₁ c₂ : Comodule k H M}
    (hd : ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
      @differential k H M _ _ _ _ _ c₁ d m = @differential k H M _ _ _ _ _ c₂ d m) : c₁ = c₂ := by
  have hcoact := (@LinearMap.map_coact_iff_map_differential_of_geometricallyConnected
    k _ _ H _ M _ _ c₁ M _ _ c₂ hH LinearMap.id).mpr hd
  ext m
  simpa only [TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id] using
    LinearMap.congr_fun hcoact m

/-- Over any field of characteristic zero, rational invariants of a geometrically connected
finite-type affine group are exactly the vectors killed by every tangent vector. -/
theorem coact_eq_tmul_one_iff_forall_differential_eq_zero_of_geometricallyConnected
    (hH : geometricallyConnectedCommHopfAlgProperty k H) {V : Type w} [AddCommGroup V] [Module k V]
    [Comodule k H V] (v : V) :
    coact (R := k) (C := H) v = v ⊗ₜ[k] (1 : H) ↔
      ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
        differential (R := k) (H := H) d v = 0 := by
  refine ⟨fun hv ↦ differential_eq_zero_of_coact_eq_tmul_one hv, fun hv ↦ ?_⟩
  let : Comodule k H k := trivial
  let f : k →ₗ[k] V := LinearMap.toSpanSingleton k V v
  have hf := (f.map_coact_iff_map_differential_of_geometricallyConnected hH).mpr fun d a ↦ by
    rw [differential_eq_zero_of_coact_eq_tmul_one (trivial_coact_apply a) d, map_zero]
    simp [f, hv]
  simpa [f] using (LinearMap.congr_fun hf 1).symm

end GeometricallyConnected

/-- For a connected affine group over an algebraically closed field of characteristic zero, two
rational representation structures on the same vector space coincide if their differentiated
Lie-algebra actions agree. No finite-dimensionality assumption is needed. -/
theorem ext_of_differential_eq {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
    {M : Type w} [AddCommGroup M] [Module k M] {c₁ c₂ : Comodule k H M}
    (hd : ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
      @differential k H M _ _ _ _ _ c₁ d m = @differential k H M _ _ _ _ _ c₂ d m) : c₁ = c₂ :=
  ext_of_differential_eq_of_geometricallyConnected
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr inferInstance) hd

/-- For a connected affine group over an algebraically closed field of characteristic zero,
rational invariants are exactly the vectors killed by every tangent vector.
No dimension assumption is needed. -/
theorem coact_eq_tmul_one_iff_forall_differential_eq_zero
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
    {V : Type w} [AddCommGroup V] [Module k V] [Comodule k H V] (v : V) :
    coact (R := k) (C := H) v = v ⊗ₜ[k] (1 : H) ↔
      ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
        differential (R := k) (H := H) d v = 0 :=
  coact_eq_tmul_one_iff_forall_differential_eq_zero_of_geometricallyConnected
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr inferInstance) v

end TauCeti.Comodule
