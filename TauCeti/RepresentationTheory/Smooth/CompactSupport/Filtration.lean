/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.CompactSupport.OpenClosed
public import TauCeti.Topology.LocallyConstant.CompactSupport.Filtration
public import TauCeti.GroupTheory.GroupAction.SubMulAction

/-!
# The equivariant filtration of compactly supported functions by stable open subsets

Let a group `G` act on a topological space `X` by homeomorphisms. For a `G`-stable subset `U`,
the functions in `C_c^∞(X, M)` vanishing off `U` (`LocallyConstant.compactlySupportedIn`) are
stable under translation, giving a representation `TauCeti.compactlySupportedInRep R G U M` and an
intertwining inclusion into `TauCeti.compactlySupportedRep R G X M`. For `G`-stable open subsets
`V` and `W` of an l-space, restriction to the `G`-stable locally closed stratum `W ∩ Vᶜ` is an
intertwining map, and it identifies the successive quotient of the filtration with the
translation representation on compact sections over the stratum
(`TauCeti.compactlySupportedStratumEquiv`). Iterated along a finite filtration of `X` by
`G`-stable open subsets, this is the filtration form of the open-closed exact sequence.

## Main definitions

* `TauCeti.compactlySupportedInRep R G U M`: translation on the functions vanishing off `U`.
* `TauCeti.compactlySupportedInIncl`: its inclusion into `C_c^∞(X, M)`.
* `TauCeti.compactlySupportedRestrictStratum`: restriction to the stratum `W ∩ Vᶜ`, as an
  intertwining map.
* `TauCeti.compactlySupportedStratumEquiv`: the successive quotient of the filtration is
  isomorphic, as a representation, to the translation representation on `C_c^∞(W ∩ Vᶜ, M)`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

noncomputable section

open Function

namespace TauCeti

section Semiring

variable {R G X M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Group G]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

theorem translate_mem_compactlySupportedIn (U : SubMulAction G X) (g : G)
    {f : LocallyConstant X M} (hf : f ∈ LocallyConstant.compactlySupportedIn R M (U : Set X)) :
    LocallyConstant.comapₗ R ⟨(g⁻¹ • ·), continuous_const_smul _⟩ f ∈
      LocallyConstant.compactlySupportedIn R M (U : Set X) := by
  rw [LocallyConstant.mem_compactlySupportedIn] at hf ⊢
  refine ⟨hf.1.comp_homeomorph (Homeomorph.smul g⁻¹), fun x hx => ?_⟩
  have hx' : g⁻¹ • x ∉ U := fun h => hx (by simpa using U.smul_mem g h)
  simpa using hf.2 _ hx'

variable (R G M) in
/-- **The translation representation on the functions vanishing off a `G`-stable subset `U`**:
`(g • f)(x) = f(g⁻¹ • x)` on `C_c^∞(X, M)_U`. -/
def compactlySupportedInRep (U : SubMulAction G X) :
    Representation R G (LocallyConstant.compactlySupportedIn R M (U : Set X)) where
  toFun g := (LocallyConstant.comapₗ R ⟨(g⁻¹ • ·), continuous_const_smul _⟩).restrict
    fun _ hf => translate_mem_compactlySupportedIn U g hf
  map_one' := LinearMap.ext fun _ => Subtype.ext <| LocallyConstant.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun f => Subtype.ext <| LocallyConstant.ext fun x => by
    simp [mul_smul]

@[simp]
theorem compactlySupportedInRep_apply_coe (U : SubMulAction G X) (g : G)
    (f : LocallyConstant.compactlySupportedIn R M (U : Set X)) (x : X) :
    (compactlySupportedInRep R G M U g f : LocallyConstant X M) x =
      (f : LocallyConstant X M) (g⁻¹ • x) :=
  (rfl)

/-- The inclusion of the functions vanishing off a `G`-stable subset `U` into `C_c^∞(X, M)`, as an
intertwining map. -/
def compactlySupportedInIncl (U : SubMulAction G X) :
    (compactlySupportedInRep R G M U).IntertwiningMap (compactlySupportedRep R G X M) where
  toLinearMap := Submodule.inclusion
    (LocallyConstant.compactlySupportedIn_le_compactlySupported (U : Set X))
  isIntertwining' _ := LinearMap.ext fun _ => LocallyConstant.compactlySupported.ext fun _ => by
    simp [Submodule.coe_inclusion]

@[simp]
theorem coe_compactlySupportedInIncl_apply (U : SubMulAction G X)
    (f : LocallyConstant.compactlySupportedIn R M (U : Set X)) :
    ((compactlySupportedInIncl U f : LocallyConstant.compactlySupported R X M) :
      LocallyConstant X M) = f := by
  simp [compactlySupportedInIncl]

theorem compactlySupportedInIncl_injective (U : SubMulAction G X) :
    Injective (compactlySupportedInIncl (R := R) (M := M) U) :=
  Submodule.inclusion_injective (LocallyConstant.compactlySupportedIn_le_compactlySupported _)

/-- **Restriction to a stratum is equivariant**: for `G`-stable subsets `V` (open) and `W` of `X`,
restriction from the functions vanishing off `W` to the stratum `W ∩ Vᶜ` intertwines the
translation representations. -/
def compactlySupportedRestrictStratum (V W : SubMulAction G X) (hV : IsOpen (V : Set X)) :
    (compactlySupportedInRep R G M W).IntertwiningMap
      (compactlySupportedRep R G (W ⊓ Vᶜ : SubMulAction G X) M) where
  toLinearMap := LocallyConstant.restrictStratum R M hV W (SubMulAction.coe_inf_compl W V)
  isIntertwining' g := LinearMap.ext fun f => LocallyConstant.compactlySupported.ext fun z => by
    simp [LocallyConstant.restrictStratum_apply hV (SubMulAction.coe_inf_compl W V)]

@[simp]
theorem coe_compactlySupportedRestrictStratum (V W : SubMulAction G X)
    (hV : IsOpen (V : Set X)) :
    ⇑(compactlySupportedRestrictStratum (R := R) (M := M) V W hV) =
      LocallyConstant.restrictStratum R M hV W (SubMulAction.coe_inf_compl W V) :=
  (rfl)

@[simp]
theorem toLinearMap_compactlySupportedRestrictStratum (V W : SubMulAction G X)
    (hV : IsOpen (V : Set X)) :
    (compactlySupportedRestrictStratum (R := R) (M := M) V W hV).toLinearMap =
      LocallyConstant.restrictStratum R M hV W (SubMulAction.coe_inf_compl W V) :=
  (rfl)

end Semiring

section Ring

variable {R G X M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

variable (R G M) in
/-- The functions vanishing off `V` form a subrepresentation of those vanishing off `W`, so the
successive quotient of the filtration carries the quotient representation. -/
def compactlySupportedStratumRep (V W : SubMulAction G X) :
    Representation R G (LocallyConstant.compactlySupportedIn R M (W : Set X) ⧸
      (LocallyConstant.compactlySupportedIn R M (V : Set X)).comap
        (LocallyConstant.compactlySupportedIn R M (W : Set X)).subtype) :=
  (compactlySupportedInRep R G M W).quotient _ fun g _ hf =>
    translate_mem_compactlySupportedIn V g hf

@[simp]
theorem compactlySupportedStratumRep_mk (V W : SubMulAction G X) (g : G)
    (f : LocallyConstant.compactlySupportedIn R M (W : Set X)) :
    compactlySupportedStratumRep R G M V W g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (compactlySupportedInRep R G M W g f) :=
  (rfl)

variable [T2Space X] [WeaklyLocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- **The successive quotients of the equivariant filtration**: for `G`-stable open subsets `V`
and `W` of an l-space, restriction identifies the quotient of the functions vanishing off `W` by
those vanishing off `V` with the translation representation on `C_c^∞(W ∩ Vᶜ, M)`. -/
def compactlySupportedStratumEquiv (V W : SubMulAction G X) (hV : IsOpen (V : Set X))
    (hW : IsOpen (W : Set X)) :
    (compactlySupportedStratumRep R G M V W).Equiv
      (compactlySupportedRep R G (W ⊓ Vᶜ : SubMulAction G X) M) :=
  .mk (LocallyConstant.stratumEquiv R M hV hW (SubMulAction.coe_inf_compl W V)) fun g =>
    Submodule.linearMap_qext _ <| LinearMap.ext fun f =>
      LocallyConstant.compactlySupported.ext fun z => by
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
          compactlySupportedStratumRep_mk]
        rw [LocallyConstant.stratumEquiv_mk, LocallyConstant.stratumEquiv_mk]
        simp [LocallyConstant.restrictStratum_apply hV (SubMulAction.coe_inf_compl W V)]

@[simp]
theorem compactlySupportedStratumEquiv_mk (V W : SubMulAction G X) (hV : IsOpen (V : Set X))
    (hW : IsOpen (W : Set X)) (f : LocallyConstant.compactlySupportedIn R M (W : Set X)) :
    compactlySupportedStratumEquiv (R := R) (M := M) V W hV hW (Submodule.Quotient.mk f) =
      LocallyConstant.restrictStratum R M hV W (SubMulAction.coe_inf_compl W V) f :=
  (Representation.Equiv.mk_apply _ _).trans (LocallyConstant.stratumEquiv_mk _ _ _ _)

end Ring

end TauCeti
