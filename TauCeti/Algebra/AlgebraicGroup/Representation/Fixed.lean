/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
import TauCeti.Algebra.Coalgebra.Comodule.Product
import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Fixed vectors and differentiation

For a connected affine group over an algebraically closed field of characteristic zero,
a vector in a rational representation is fixed exactly when its differentiated action is
zero. More generally, a linear map intertwines rational representations exactly when it
intertwines their differentials. Neither representation needs to be finite dimensional.

The morphism criterion follows by applying the Lie-stable subspace criterion to the graph
of the linear map. Applying it to a map from the trivial representation gives the fixed
vector criterion. In particular this allows infinitesimal invariants, such as the center
of the tangent Lie algebra, to be recognized as rational invariants.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.

The graph argument uses `Submodule.coact_mem_range_of_forall_differential_mem`.
-/

public section

open TauCeti
open scoped TensorProduct

universe u w x

namespace LinearMap

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
variable {N : Type x} [AddCommGroup N] [Module k N] [Comodule k H N]

/-- For a connected affine group in characteristic zero, a linear map is a rational
representation morphism exactly when it intertwines the differentiated actions. -/
theorem map_coact_iff_map_differential (f : M →ₗ[k] N) :
    TensorProduct.map f LinearMap.id ∘ₗ Comodule.coact (R := k) (C := H) =
        Comodule.coact (R := k) (C := H) ∘ₗ f ↔
      ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
        f (Comodule.differential (R := k) (H := H) d m) =
          Comodule.differential (R := k) (H := H) d (f m) := by
  constructor
  · intro hf
    exact (Comodule.Hom.map_differential ⟨f, hf⟩)
  · intro hf
    let : Comodule k H (M × N) := Comodule.Prod
    have hgraph : ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)), ∀ z ∈ f.graph,
        Comodule.differential (R := k) (H := H) d z ∈ f.graph := by
      intro d z hz
      have hfst := (Comodule.prodFst (R := k) (C := H) (M := M) (N := N)).map_differential d z
      have hsnd := (Comodule.prodSnd (R := k) (C := H) (M := M) (N := N)).map_differential d z
      simp only [Comodule.prodFst_apply] at hfst
      simp only [Comodule.prodSnd_apply] at hsnd
      rw [mem_graph_iff] at hz ⊢
      rw [hsnd, hfst, hz, hf]
    let q : M × N →ₗ[k] N := LinearMap.snd k M N - f.comp (LinearMap.fst k M N)
    have hq : q.comp f.graph.subtype = 0 := by
      ext z
      exact sub_eq_zero.mpr ((mem_graph_iff f z).mp z.2)
    ext m
    obtain ⟨t, ht⟩ := f.graph.coact_mem_range_of_forall_differential_mem hgraph
      ((mem_graph_iff f (m, f m)).mpr rfl)
    have hzero : q.rTensor H (Comodule.coact (R := k) (C := H) (m, f m)) = 0 := by
      rw [← ht, ← rTensor_def, ← rTensor_comp_apply, hq, rTensor_zero, zero_apply]
    have hfst := (Comodule.prodFst (R := k) (C := H) (M := M) (N := N)).map_coact_apply
      (m, f m)
    have hsnd := (Comodule.prodSnd (R := k) (C := H) (M := M) (N := N)).map_coact_apply
      (m, f m)
    simp only [Comodule.prodFst_toLinearMap, Comodule.prodFst_apply] at hfst
    simp only [Comodule.prodSnd_toLinearMap, Comodule.prodSnd_apply] at hsnd
    rw [rTensor_sub, LinearMap.sub_apply, rTensor_comp_apply] at hzero
    simp only [rTensor_def] at hzero
    rw [hsnd, hfst] at hzero
    exact (sub_eq_zero.mp hzero).symm

end LinearMap

namespace TauCeti.Comodule

/-- For a connected affine group in characteristic zero, rational invariants are exactly
the vectors killed by every tangent vector. No dimension assumption is needed. -/
theorem coact_eq_tmul_one_iff_forall_differential_eq_zero
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
    {V : Type w} [AddCommGroup V] [Module k V] [Comodule k H V] (v : V) :
    coact (R := k) (C := H) v = v ⊗ₜ[k] (1 : H) ↔
      ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
        differential (R := k) (H := H) d v = 0 := by
  constructor
  · exact fun hv ↦ differential_eq_zero_of_coact_eq_tmul_one hv
  · intro hv
    let : Comodule k H k := trivial
    let f : k →ₗ[k] V := LinearMap.toSpanSingleton k V v
    have hf := (f.map_coact_iff_map_differential (H := H)).mpr (by
      intro d a
      have ha : differential (R := k) (H := H) d a = 0 :=
        differential_eq_zero_of_coact_eq_tmul_one (trivial_coact_apply a) d
      rw [ha, map_zero]
      simp [f, hv])
    have h := LinearMap.congr_fun hf 1
    simpa [f] using h.symm

end TauCeti.Comodule
