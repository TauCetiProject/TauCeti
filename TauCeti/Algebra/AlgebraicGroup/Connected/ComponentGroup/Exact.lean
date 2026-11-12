/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Idempotent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants

/-!
# Exactness of the component-group sequence

For a faithfully flat homomorphism `G → Q` of finite-type affine groups over an algebraically
closed field, with scheme-theoretic kernel `N`, the sequence
`π₀(N) → π₀(G) → π₀(Q) → 1` is exact. No smoothness or reducedness is required.
There is no claim of injectivity at the left: a disconnected subgroup can lie in a connected
group.

The main step identifies the kernel of the component homomorphism. The union of components
of `G` meeting `N` is cut out by an idempotent function invariant under `N`. Faithfully flat
descent puts this function in `O(Q)`. Its value at the identity is one, so it is one on the
entire identity component of `Q`.

The proof uses `componentFunctionAlgHom`, rational detection of invariant idempotents, and
`CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, identity components and quotients.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7 and 16.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A component mapping to the identity component meets the scheme-theoretic kernel. -/
private theorem exists_kernel_point_of_mapComponentGroup_eq_one (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (C : ConnectedComponents (PrimeSpectrum G)) (hC : mapComponentGroup f C = 1) :
    ∃ n ∈ CommHopfAlgCat.quotientPointsSubgroup G.obj
      (CommHopfAlgCat.kernelHopfIdeal f.hom) (CommAlgCat.of k k),
      rationalComponentMap G n = C := by
  classical
  let N := CommHopfAlgCat.quotientPointsSubgroup G.obj
    (CommHopfAlgCat.kernelHopfIdeal f.hom) (CommAlgCat.of k k)
  let S := N.map (rationalComponentMap G)
  let indicator : ConnectedComponents (PrimeSpectrum G) → k := fun D ↦ if D ∈ S then 1 else 0
  let e := componentFunctionAlgHom G indicator
  have hi : IsIdempotentElem indicator := by
    ext D
    simp only [indicator, Pi.mul_apply]
    split_ifs <;> simp
  have he : IsIdempotentElem e := hi.map (componentFunctionAlgHom G)
  have heval (g : HopfAlgebra.points (R := k) (H := G) (CommAlgCat.of k k)) :
      g.ofConv e = indicator (rationalComponentMap G g) :=
    eval_componentFunctionAlgHom G g indicator
  -- The components meeting the kernel form a subgroup, so their indicator is invariant.
  have hecoinv : e ∈ (CommHopfAlgCat.kernelHopfIdeal f.hom).coinvariants := by
    apply (HopfIdeal.mem_coinvariants_iff_forall_mul_of_isIdempotentElem (K := k) _ he).mpr
    intro g n hn
    have hnS : rationalComponentMap G n ∈ S := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    simp only [heval, map_mul, indicator, S.mul_mem_cancel_right hnS]
  obtain ⟨a, haidem, ha⟩ :=
    f.hom.exists_map_eq_of_isIdempotentElem_mem_coinvariants hf he hecoinv
  have hε : (Bialgebra.counitAlgHom k Q) a = 1 := by
    calc
      Bialgebra.counitAlgHom k Q a = Bialgebra.counitAlgHom k G (f.hom.hom a) :=
        (AlgHom.congr_fun (BialgHom.counitAlgHom_comp f.hom.hom) a).symm
      _ = 1 := by
        rw [ha, Bialgebra.counitAlgHom_apply, counit_componentFunctionAlgHom]
        simp only [indicator, Subgroup.one_mem, ite_true]
  obtain ⟨g, hg⟩ := rationalComponentMap_surjective G C
  let q := BialgHom.mapDomain (A := k) f.hom.hom g
  have hq : rationalComponentMap Q q = 1 := by
    rw [← mapComponentGroup_rationalComponentMap f, hg, hC]
  -- The descended idempotent is nonzero on the whole identity component.
  have hnonzero : q.ofConv a ≠ 0 :=
    ofConv_ne_zero_of_isIdempotentElem_of_rationalComponentMap_eq_one Q haidem
      (hε.trans_ne one_ne_zero) q hq
  have he_nonzero : g.ofConv e ≠ 0 := by
    simpa only [q, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom, ha] using hnonzero
  have hCS : C ∈ S := by
    by_contra hnot
    apply he_nonzero
    simp [heval, indicator, hg, hnot]
  exact Subgroup.mem_map.mp hCS

/-- The kernel of the component homomorphism consists exactly of the components meeting the
scheme-theoretic kernel. This holds for faithfully flat maps between finite-type affine groups
over an algebraically closed field, including nonreduced groups in positive characteristic. -/
theorem ker_mapComponentGroup (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    (mapComponentGroup f).ker =
      (CommHopfAlgCat.quotientPointsSubgroup G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
        (CommAlgCat.of k k)).map (rationalComponentMap G) := by
  ext C
  constructor
  · exact fun hC ↦ Subgroup.mem_map.mpr
      (exists_kernel_point_of_mapComponentGroup_eq_one f hf C hC)
  · rintro ⟨n, hn, rfl⟩
    rw [MonoidHom.mem_ker, mapComponentGroup_rationalComponentMap]
    have hn' := (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f.hom _ n).mpr hn
    rw [← BialgHom.mapDomain_apply] at hn'
    rw [hn', map_one]

/-- **Exactness on component groups.** For a faithfully flat homomorphism `G → Q` with
scheme-theoretic kernel `N`, the sequence `π₀(N) → π₀(G) → π₀(Q)` is exact.
The final map is also surjective by `mapComponentGroup_surjective_of_injective`. -/
theorem mulExact_mapComponentGroup_kernel (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    Function.MulExact
      (mapComponentGroup (mkQuotient G (CommHopfAlgCat.kernelHopfIdeal f.hom)))
      (mapComponentGroup f) := by
  intro C
  rw [← MonoidHom.mem_ker, ker_mapComponentGroup f hf]
  constructor
  · rintro ⟨n, ⟨n', rfl⟩, hn⟩
    refine ⟨rationalComponentMap (quotient G (CommHopfAlgCat.kernelHopfIdeal f.hom)) n', ?_⟩
    rw [mapComponentGroup_rationalComponentMap]
    exact hn
  · rintro ⟨D, rfl⟩
    obtain ⟨n, rfl⟩ := rationalComponentMap_surjective
      (quotient G (CommHopfAlgCat.kernelHopfIdeal f.hom)) D
    rw [mapComponentGroup_rationalComponentMap]
    exact Subgroup.mem_map.mpr ⟨_,
      CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup G.obj
        (CommHopfAlgCat.kernelHopfIdeal f.hom) (CommAlgCat.of k k) n, rfl⟩

end TauCeti.FiniteTypeCommHopfAlgCat
