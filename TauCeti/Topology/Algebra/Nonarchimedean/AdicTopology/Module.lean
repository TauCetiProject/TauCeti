/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Maps.Strict.Basic
public import TauCeti.RingTheory.Ideal.ArtinRees
public import TauCeti.Topology.Algebra.Nonarchimedean.SubmodulesBasis

/-!
# Adic topologies on modules

For an ideal `I` of a commutative ring, every linear map is continuous for the `I`-adic
module topologies, and every surjective linear map is an open quotient map. These assertions
need neither finite generation nor completeness.

Over a noetherian ring, Artin–Rees shows that a submodule of a finite module has its adic
topology as its subspace topology. Consequently every linear map into a finite module is
strict: the quotient by its kernel has the topology induced on its image. In particular,
linear maps between finite adic modules are continuous and strict. This is the topological
input for treating finite modules as coherent modules on affine formal schemes.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. 0, §§7.2–7.3, especially Corollaire 7.3.6.
-/

public section

open Filter Topology

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace Ideal

/-- The powers `I^n M` form a neighbourhood basis of zero for the adic module topology. -/
theorem hasBasis_nhds_zero_adicModule (I : Ideal R) :
    (@nhds M (I.adicModuleTopology M) 0).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (↑(I ^ n • (⊤ : Submodule R M)) : Set M)) := by
  let := I.adicTopology
  exact (I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis M)).hasBasis_nhds_zero

end Ideal

namespace LinearMap

/-- Every linear map is continuous for the adic module topologies. -/
theorem continuous_adicModuleTopology (f : M →ₗ[R] N) (I : Ideal R) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let := I.adicTopology
  let := I.adicModuleTopology M
  let := I.adicModuleTopology N
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  exact (I.hasBasis_nhds_zero_adicModule.tendsto_iff
    I.hasBasis_nhds_zero_adicModule).mpr fun n _ ↦
      ⟨n, trivial, Submodule.smul_top_le_comap_smul_top (I ^ n) f⟩

/-- A surjective linear map is an open quotient map for adic module topologies, without
finiteness or completeness assumptions. In particular, adic module topology commutes with
quotients. -/
theorem isOpenQuotientMap_adicModuleTopology (f : M →ₗ[R] N) (I : Ideal R)
    (hf : Function.Surjective f) :
    @IsOpenQuotientMap M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let := I.adicTopology
  let := I.adicModuleTopology M
  let := I.adicModuleTopology N
  refine ⟨hf, f.continuous_adicModuleTopology I, ?_⟩
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  have hmap (n : ℕ) : f '' (↑(I ^ n • (⊤ : Submodule R M)) : Set M) =
      (↑(I ^ n • (⊤ : Submodule R N)) : Set N) := by
    rw [← Submodule.map_coe, Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr hf]
  exact ((I.hasBasis_nhds_zero_adicModule (M := N)).le_basis_iff
    ((I.hasBasis_nhds_zero_adicModule (M := M)).map f)).mpr
      fun n _ ↦ ⟨n, trivial, (hmap n).ge⟩

end LinearMap

namespace Submodule

/-- Artin–Rees makes the adic topology of a submodule of a finite module over a noetherian
ring equal to its subspace topology. No completeness or separatedness is required. -/
theorem isEmbedding_subtype_adicModuleTopology [IsNoetherianRing R] [Module.Finite R M]
    (P : Submodule R M) (I : Ideal R) :
    @Topology.IsEmbedding P M (I.adicModuleTopology P) (I.adicModuleTopology M) P.subtype := by
  let := I.adicTopology
  let := I.adicModuleTopology M
  let := I.adicModuleTopology P
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_, P.injective_subtype⟩
  refine le_antisymm ?_ ?_
  · exact Filter.map_le_iff_le_comap.mp
      (by simpa only [ContinuousAt, Filter.Tendsto, map_zero] using
        (P.subtype.continuous_adicModuleTopology I).continuousAt (x := 0))
  obtain ⟨k, hk⟩ := TauCeti.ArtinRees.exists_controlled_lift I P
  refine ((I.hasBasis_nhds_zero_adicModule (M := M)).comap P.subtype).le_basis_iff
    (I.hasBasis_nhds_zero_adicModule (M := P)) |>.mpr ?_
  intro n _
  refine ⟨n + k, trivial, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hk (LinearMap.id : P →ₗ[R] P) Function.surjective_id n x hx
  exact hxy ▸ hy

end Submodule

namespace LinearMap

/-- Every linear map into a finite module over a noetherian ring is strict for adic module
topologies. The source need not be finite: its quotient topology on the image is always adic,
and Artin–Rees identifies this with the subspace topology in the finite target. -/
theorem isStrictMap_adicModuleTopology [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (I : Ideal R) :
    @Topology.IsStrictMap M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let := I.adicTopology
  let := I.adicModuleTopology M
  let := I.adicModuleTopology N
  let := I.adicModuleTopology (LinearMap.range f)
  have hi := (LinearMap.range f).isEmbedding_subtype_adicModuleTopology I
  have hq := f.rangeRestrict.isOpenQuotientMap_adicModuleTopology I f.surjective_rangeRestrict
  exact hi.isStrictMap_iff.mp hq.isQuotientMap.isStrictMap

end LinearMap
