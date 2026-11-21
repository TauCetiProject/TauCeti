/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Lattice
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
import TauCeti.LinearAlgebra.Basis.RangeSpan

/-!
# The stabilizer of a lattice is `GL_n` of the coefficient ring

Let `R → K` be a map of commutative rings, `V` a `K`-module and `L ⊆ V` a full `R`-lattice
(`Submodule.IsFullLattice K L`), for instance a lattice over the valuation ring of a
nonarchimedean local field `K`. A linear automorphism `g` of `V` stabilizes `L`, in the sense
that `g L = L`, exactly when it restricts to an `R`-linear automorphism of `L`. Since `L` spans
`V` over `K`, the restriction determines `g`, and when `L` is free every `R`-linear automorphism
of `L` extends to `V`. So the stabilizer of `L` in `V ≃ₗ[K] V` is the group `L ≃ₗ[R] L`
(`LinearEquiv.restrictStabilizerEquiv`).

In an `R`-basis `b` of `L` of size `n`, which is also a `K`-basis of `V`
(`Module.Basis.extendOfIsFullLattice`), this says that the stabilizer is `GL_n(R)`:
`Module.Basis.stabilizerEquivGL b` identifies it with `GL ι R`, compatibly with the matrices of
automorphisms of `V` in the extended basis (`Module.Basis.map_stabilizerEquivGL`), and an
automorphism of `V` stabilizes `L` exactly when its matrix in that basis has entries in `R`
together with its inverse (`Module.Basis.mem_stabilizer_iff_toGL_mem_range`). When `K` is a
topological ring, `V` carries its module topology and `R` carries the topology induced from
`K`, the identification is a homeomorphism (`Module.Basis.stabilizerContinuousMulEquivGL`). Over
a nonarchimedean local field `E` this identifies the compact open stabilizer of an
`𝒪[E]`-lattice with `GL_n(𝒪[E])`.

## Main definitions

* `LinearEquiv.restrictStabilizer`: restriction of the stabilizer of a submodule to it.
* `LinearEquiv.restrictStabilizerEquiv`: for a free full lattice, restriction is an isomorphism
  onto the linear automorphisms of the lattice.
* `Module.Basis.stabilizerEquivGL`: the stabilizer of a lattice with a basis is `GL ι R`.
* `Module.Basis.stabilizerContinuousMulEquivGL`: the same identification as topological groups.

## Main results

* `Module.Basis.map_stabilizerEquivGL`: the matrix over `R` of an element of the stabilizer maps
  to its matrix over `K` in the extended basis.
* `Module.Basis.mem_stabilizer_iff_toGL_mem_range`,
  `Module.Basis.map_toGL_stabilizer`: in the extended basis, the stabilizer of the lattice is the
  image of `GL ι R` in `GL ι K`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, paragraph after
  Proposition 2.6.
-/

public section

open Module Set Submodule
open scoped Pointwise

section Restrict

variable {R K V : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- An element of the stabilizer of the underlying set of a submodule maps the submodule onto
itself. -/
theorem Submodule.map_restrictScalars_eq_of_mem_stabilizer (L : Submodule R V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    L.map ((g : V ≃ₗ[K] V).restrictScalars R : V →ₗ[R] V) = L := by
  apply SetLike.coe_injective
  rw [Submodule.map_coe]
  simpa [← Set.image_smul, LinearEquiv.smul_def] using MulAction.mem_stabilizer_iff.mp g.2

namespace LinearEquiv

/-- **Restriction of the stabilizer of a submodule.** A `K`-linear automorphism of `V` mapping
the `R`-submodule `L` onto itself restricts to an `R`-linear automorphism of `L`. -/
def restrictStabilizer (L : Submodule R V) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) →* (L ≃ₗ[R] L) where
  toFun g := ((g : V ≃ₗ[K] V).restrictScalars R).ofSubmodules L L
    (map_restrictScalars_eq_of_mem_stabilizer L g)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The restriction of `g` acts on the submodule as `g` does. -/
@[simp]
theorem coe_restrictStabilizer_apply (L : Submodule R V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) (x : L) :
    (restrictStabilizer L g x : V) = (g : V ≃ₗ[K] V) x :=
  (rfl)

/-- Restriction to a submodule spanning `V` over `K` is injective on its stabilizer. -/
theorem restrictStabilizer_injective (L : Submodule R V) (hL : span K (L : Set V) = ⊤) :
    Function.Injective (restrictStabilizer (K := K) L) := by
  intro g h hgh
  refine Subtype.ext (toLinearMap_injective (LinearMap.ext_on hL fun x hx => ?_))
  simpa using congrArg Subtype.val (LinearEquiv.congr_fun hgh ⟨x, hx⟩)

end LinearEquiv

end Restrict

namespace LinearEquiv

section FullLattice

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Every linear automorphism of a free full lattice extends to an automorphism of the ambient
module stabilizing the lattice. -/
theorem restrictStabilizer_surjective (L : Submodule R V) [L.IsFullLattice K] [Module.Free R L] :
    Function.Surjective (restrictStabilizer (K := K) L) := by
  intro e
  refine ⟨⟨LinearEquiv.extendOfIsFullLattice (K := K) e, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    have h := congrArg ((↑) : Submodule R V → Set V) (LinearEquiv.extendOfIsFullLattice_map
      (K := K) e)
    rw [Submodule.map_coe] at h
    simpa [← Set.image_smul, LinearEquiv.smul_def] using h
  · ext x
    exact LinearEquiv.extendOfIsFullLattice_apply e x

/-- **The stabilizer of a free full lattice is its linear automorphism group.** For a free full
`R`-lattice `L` in the `K`-module `V`, restriction identifies the stabilizer of `L` in
`V ≃ₗ[K] V` with `L ≃ₗ[R] L`. -/
noncomputable def restrictStabilizerEquiv (L : Submodule R V) [L.IsFullLattice K]
    [Module.Free R L] :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* (L ≃ₗ[R] L) :=
  MulEquiv.ofBijective (restrictStabilizer L)
    ⟨restrictStabilizer_injective L IsFullLattice.span_eq_top, restrictStabilizer_surjective L⟩

/-- The isomorphism `restrictStabilizerEquiv L` is restriction to `L`. -/
@[simp]
theorem coe_restrictStabilizerEquiv (L : Submodule R V) [L.IsFullLattice K] [Module.Free R L] :
    ((restrictStabilizerEquiv L : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* (L ≃ₗ[R] L)) :
      MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) → (L ≃ₗ[R] L)) = restrictStabilizer L :=
  (rfl)

/-- The inverse of `restrictStabilizerEquiv L` extends an automorphism of `L` to `V`. -/
@[simp]
theorem coe_restrictStabilizerEquiv_symm_apply (L : Submodule R V) [L.IsFullLattice K]
    [Module.Free R L] (e : L ≃ₗ[R] L) :
    ((restrictStabilizerEquiv (K := K) L).symm e : V ≃ₗ[K] V) =
      LinearEquiv.extendOfIsFullLattice e :=
  LinearEquiv.eq_extendOfIsFullLattice e _ fun x => by
    rw [← coe_restrictStabilizer_apply, ← coe_restrictStabilizerEquiv (K := K) L,
      MulEquiv.apply_symm_apply]

end FullLattice

end LinearEquiv

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  {L : Submodule R V} [L.IsFullLattice K]

variable [Fintype ι] [DecidableEq ι]

/-- **The stabilizer of a lattice is `GL_n(R)`.** An `R`-basis `b` of the full lattice `L`
identifies the stabilizer of `L` in `V ≃ₗ[K] V` with `GL ι R`, sending `g` to the matrix of its
restriction to `L`. -/
noncomputable def stabilizerEquivGL (b : Basis ι R L) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* GL ι R :=
  haveI := Module.Free.of_basis b
  (LinearEquiv.restrictStabilizerEquiv L).trans b.toGL

/-- The matrix of `g` over `R` is the matrix in `b` of its restriction to `L`, as an element of
`GL ι R`. -/
theorem stabilizerEquivGL_apply (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    b.stabilizerEquivGL g = b.toGL (LinearEquiv.restrictStabilizer L g) :=
  (rfl)

/-- The matrix over `R` of an element `g` of the stabilizer of `L` is the matrix of its restriction
to `L` in the basis `b`. -/
@[simp]
theorem coe_stabilizerEquivGL_apply (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    (b.stabilizerEquivGL g : Matrix ι ι R) =
      LinearMap.toMatrix b b (LinearEquiv.restrictStabilizer L g) := by
  rw [stabilizerEquivGL_apply, coe_toGL]

/-- The matrix over `R` of an element `g` of the stabilizer of `L` maps to the matrix of `g` in
the extended basis of `V`. -/
@[simp]
theorem map_stabilizerEquivGL (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (b.stabilizerEquivGL g) =
      (b.extendOfIsFullLattice K).toGL g := by
  ext i j
  simp [coe_toGL, LinearMap.toMatrix_apply, ← extendOfIsFullLattice_repr_apply]

/-- The matrix in the extended basis of the automorphism of `V` corresponding to `A : GL ι R` is
the image of `A` in `GL ι K`. -/
@[simp]
theorem toGL_stabilizerEquivGL_symm (b : Basis ι R L) (A : GL ι R) :
    (b.extendOfIsFullLattice K).toGL ((b.stabilizerEquivGL (K := K)).symm A : V ≃ₗ[K] V) =
      Matrix.GeneralLinearGroup.map (algebraMap R K) A := by
  rw [← map_stabilizerEquivGL, MulEquiv.apply_symm_apply]

/-- **The stabilizer of a lattice in a basis.** An automorphism `g` of `V` stabilizes the full
lattice `L` with basis `b` exactly when its matrix in the extended basis of `V` comes from
`GL ι R`, that is, when the matrices of `g` and `g⁻¹` have entries in `R`. -/
theorem mem_stabilizer_iff_toGL_mem_range (b : Basis ι R L) (g : V ≃ₗ[K] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ↔
      (b.extendOfIsFullLattice K).toGL g ∈
        (Matrix.GeneralLinearGroup.map (algebraMap R K)).range := by
  refine ⟨fun hg => ⟨b.stabilizerEquivGL ⟨g, hg⟩, map_stabilizerEquivGL b ⟨g, hg⟩⟩, ?_⟩
  rintro ⟨A, hA⟩
  have hmat (h : V ≃ₗ[K] V) (B : GL ι R)
      (hB : Matrix.GeneralLinearGroup.map (algebraMap R K) B = (b.extendOfIsFullLattice K).toGL h) :
      MapsTo h L L := by
    have hm := (b.extendOfIsFullLattice K).mapsTo_span_range_iff_forall_toMatrix_mem (A := R)
      h.toLinearMap
    rw [b.span_range_extendOfIsFullLattice] at hm
    exact hm.mpr fun i j => ⟨B i j, by rw [← coe_toGL, ← hB, Matrix.GeneralLinearGroup.map_apply]⟩
  refine TauCeti.mem_stabilizer_set_iff_mapsTo.mpr ⟨hmat g A hA, hmat g⁻¹ A⁻¹ ?_⟩
  rw [map_inv, map_inv, hA]

/-- **The stabilizer of a lattice is `GL_n(R)` inside `GL_n(K)`.** In the extended basis, the
stabilizer of `L` corresponds to the image of `GL ι R` in `GL ι K`. -/
theorem map_toGL_stabilizer (b : Basis ι R L) :
    (MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)).map
        (b.extendOfIsFullLattice K).toGL.toMonoidHom =
      (Matrix.GeneralLinearGroup.map (algebraMap R K)).range := by
  ext A
  rw [Subgroup.mem_map_equiv, mem_stabilizer_iff_toGL_mem_range b, MulEquiv.apply_symm_apply]

section Topology

variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalSemiring K]
  [TopologicalSpace V] [IsModuleTopology K V]

/-- **The stabilizer of a lattice is `GL_n(R)` as a topological group.** When `R` carries the
topology induced from the topological ring `K` and `V` its `K`-module topology, the
identification of the stabilizer of `L` in `V ≃ₗ[K] V` with `GL ι R` in an `R`-basis of `L` is a
homeomorphism. For the valuation ring `𝒪[E]` of a valued field `E`, take
`hR := Topology.IsInducing.subtypeVal`. -/
noncomputable def stabilizerContinuousMulEquivGL (b : Basis ι R L)
    (hR : Topology.IsInducing (algebraMap R K)) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃ₜ* GL ι R where
  toMulEquiv := b.stabilizerEquivGL
  continuous_toFun := by
    set c := b.extendOfIsFullLattice K
    have : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
    -- The entries of the matrix over `R` are coordinates in `c`, read in `K`.
    have hentry (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) (i j : ι) :
        algebraMap R K ((b.stabilizerEquivGL g : Matrix ι ι R) i j) =
          c.coord i (LinearMap.applyₗ (c j) ((g : V ≃ₗ[K] V) : Module.End K V)) := by
      rw [← Matrix.GeneralLinearGroup.map_apply, map_stabilizerEquivGL]
      simp [c, coe_toGL, LinearMap.toMatrix_apply]
    have hmat {f : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) →
        MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)}
        (hf : Continuous fun g => ((f g : V ≃ₗ[K] V) : Module.End K V)) :
        Continuous fun g => (b.stabilizerEquivGL (f g) : Matrix ι ι R) :=
      continuous_matrix fun i j => hR.continuous_iff.mpr <| by
        simpa only [Function.comp_def, hentry] using
          (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp
            ((IsModuleTopology.continuous_of_linearMap
              (LinearMap.applyₗ (c j) : Module.End K V →ₗ[K] V)).comp hf)
    have hc := TauCeti.continuous_linearEquiv_iff.mp
      (continuous_subtype_val (p := (· ∈ MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V))))
    refine Units.continuous_iff.mpr ⟨hmat (f := id) hc.1, ?_⟩
    exact (hmat (f := fun g => g⁻¹) hc.2).congr fun g => by
      rw [map_inv, MulEquiv.toFun_eq_coe]
  continuous_invFun := by
    set c := b.extendOfIsFullLattice K
    have : ContinuousAdd (Module.End K V) := IsModuleTopology.toContinuousAdd K (Module.End K V)
    have : IsModuleTopology K (Matrix ι ι K) := inferInstanceAs (IsModuleTopology K (ι → ι → K))
    set e := b.stabilizerEquivGL (K := K)
    -- The endomorphism underlying the preimage of `A` has matrix `A` in the extended basis.
    have hend (A : GL ι R) :
        ((e.symm A : V ≃ₗ[K] V) : Module.End K V) =
          Matrix.toLin c c ((A : Matrix ι ι R).map (algebraMap R K)) := by
      rw [← Matrix.toLin_toMatrix c c ((e.symm A : V ≃ₗ[K] V) : Module.End K V), ← coe_toGL,
        toGL_stabilizerEquivGL_symm]
      exact congrArg (Matrix.toLin c c) (Matrix.ext fun i j => by
        rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply])
    have hcont {f : GL ι R → GL ι R} (hf : Continuous fun A => (f A : Matrix ι ι R)) :
        Continuous fun A => ((e.symm (f A) : V ≃ₗ[K] V) : Module.End K V) := by
      simp only [hend]
      exact (IsModuleTopology.continuous_of_linearMap (Matrix.toLin c c).toLinearMap).comp
        (hf.matrix_map hR.continuous)
    refine Continuous.subtype_mk (TauCeti.continuous_linearEquiv_iff.mpr
      ⟨hcont (f := id) Units.continuous_val, ?_⟩) _
    have h (A : GL ι R) : ((e.symm A : V ≃ₗ[K] V)⁻¹ : V ≃ₗ[K] V) = (e.symm A⁻¹ : V ≃ₗ[K] V) := by
      rw [map_inv, Subgroup.coe_inv]
    exact (hcont (f := fun A => A⁻¹) Units.continuous_coe_inv).congr fun A => by
      rw [← h, id_eq]

/-- The underlying group isomorphism of `stabilizerContinuousMulEquivGL` is `stabilizerEquivGL`. -/
@[simp]
theorem coe_stabilizerContinuousMulEquivGL (b : Basis ι R L)
    (hR : Topology.IsInducing (algebraMap R K)) :
    (b.stabilizerContinuousMulEquivGL hR :
      MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* GL ι R) = b.stabilizerEquivGL :=
  (rfl)

end Topology

end Module.Basis
