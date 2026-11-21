/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Inverse limits of polynomial quotients along a family of polynomials

For a family of polynomials `g : ι → R[X]`, the *polynomial-family limit*
`TauCeti.PolyFamilyLimit g = lim_i R[X]/(g i)` is the algebra of families `x i ∈ R[X]/(g i)` that
are compatible with every reduction map: whenever `g i ∣ g j`, reducing `x j` modulo `g i` gives
`x i`. It carries the topology induced from the product of the discrete quotients.

Many completions of `R[X]` are of this form: the `(X - 1)`-adic completion (along the powers of
`X - 1`), Habiro's cyclotomic completions (along products of cyclotomic polynomials, see
`TauCeti.CycloCompletion`), and the presentation of the full Habiro ring along the factorial
polynomials `(1 - X) ⋯ (1 - X ^ N)`. Different families can give the same limit: if `g` and `h`
are directed for divisibility and *mutually cofinal* (every `h j` divides some `g i` and every
`g i` divides some `h j`), then the identity of `R[X]` induces an isomorphism of topological
`R`-algebras `TauCeti.PolyFamilyLimit.cofinalEquiv : PolyFamilyLimit g ≃A[R] PolyFamilyLimit h`.
Its coordinate at `j` reduces any dominating coordinate `x i` with `h j ∣ g i`; directedness of
`g` makes this independent of the choice of `i`. This is the mechanism behind every change of
presentation of these completions.

No hypothesis on `R` is needed; in particular `R` may have torsion or be the zero ring.

## Main definitions

* `TauCeti.polyFamilyCompat g`: the subalgebra of compatible families in `∏ i, R[X]/(g i)`.
* `TauCeti.PolyFamilyLimit g`: the polynomial-family limit, with its inverse-limit topology.
* `TauCeti.PolyFamilyLimit.proj i`: the projection to `R[X]/(g i)`.
* `TauCeti.PolyFamilyLimit.liftCompatAlgHom`: the algebra map induced by a compatible family of
  algebra maps into the quotients.
* `TauCeti.PolyFamilyLimit.fromPoly g`: the map `R[X] → PolyFamilyLimit g`.
* `TauCeti.PolyFamilyLimit.projOfDvd`: the reduction to `R[X]/(p)` for a polynomial `p` dividing
  some member of the family; for a directed family it reduces any coordinate `x i` with
  `p ∣ g i` (`TauCeti.PolyFamilyLimit.projOfDvd_eq`).
* `TauCeti.PolyFamilyLimit.reduce`: for a directed family `g` dominating `h`, the continuous
  algebra map `PolyFamilyLimit g → PolyFamilyLimit h` induced by the identity of `R[X]`.
* `TauCeti.PolyFamilyLimit.cofinalEquiv`: for directed mutually cofinal families, the isomorphism
  `PolyFamilyLimit g ≃A[R] PolyFamilyLimit h`.

## Main results

* `TauCeti.PolyFamilyLimit.ext`: an element is determined by its projections.
* `TauCeti.PolyFamilyLimit.proj_liftCompatAlgHom`,
  `TauCeti.PolyFamilyLimit.liftCompatAlgHom_unique`: the universal property of the inverse limit.
* `TauCeti.PolyFamilyLimit.continuous_iff`: maps into the limit are continuous exactly when all
  their coordinates are locally constant.
* `TauCeti.PolyFamilyLimit.proj_reduce`: the coordinate equation of the comparison map: its
  coordinate at `j` is the reduction of the coordinate at any `i` with `h j ∣ g i`.
* `TauCeti.PolyFamilyLimit.reduce_comp_reduce`, `TauCeti.PolyFamilyLimit.reduce_eq_id`:
  comparison maps compose, and the comparison of a family with itself is the identity.
* `TauCeti.PolyFamilyLimit.cofinalEquiv_symm`, `TauCeti.PolyFamilyLimit.cofinalEquiv_trans`: the
  inverse of a cofinal equivalence is the reversed one, and cofinal equivalences compose under a
  third cofinal replacement.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §3.1 (the inverse limit (3.1) and the cofinal presentations (3.2)).
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {ι κ ν : Type*}

/-- The compatible families in `∏ i, R[X]/(g i)`: those `x` for which, whenever `g i ∣ g j`, the
reduction from the quotient by `g j` to the quotient by `g i` sends `x j` to `x i`. -/
noncomputable def polyFamilyCompat (g : ι → R[X]) : Subalgebra R (∀ i, AdjoinRoot (g i)) where
  carrier := {x | ∀ (i j : ι) (h : g i ∣ g j), AdjoinRoot.algHomOfDvd R (g j) (g i) h (x j) = x i}
  mul_mem' hx hy i j h := by simp only [Pi.mul_apply, map_mul, hx i j h, hy i j h]
  add_mem' hx hy i j h := by simp only [Pi.add_apply, map_add, hx i j h, hy i j h]
  algebraMap_mem' r i j h := (AdjoinRoot.algHomOfDvd R (g j) (g i) h).commutes r

theorem mem_polyFamilyCompat {g : ι → R[X]} {x : ∀ i, AdjoinRoot (g i)} :
    x ∈ polyFamilyCompat g ↔
      ∀ (i j : ι) (h : g i ∣ g j), AdjoinRoot.algHomOfDvd R (g j) (g i) h (x j) = x i :=
  Iff.rfl

/-- The polynomial-family limit `lim_i R[X]/(g i)`: the algebra of families of residues compatible
with the reductions along divisibility in the family `g`. -/
abbrev PolyFamilyLimit (g : ι → R[X]) := ↥(polyFamilyCompat g)

namespace PolyFamilyLimit

variable {g : ι → R[X]} {h : κ → R[X]} {k : ν → R[X]}

/-- The projection `lim_i R[X]/(g i) → R[X]/(g i)` to the coordinate indexed by `i`. -/
noncomputable def proj (i : ι) : PolyFamilyLimit g →ₐ[R] AdjoinRoot (g i) :=
  (Pi.evalAlgHom R (fun i ↦ AdjoinRoot (g i)) i).comp (polyFamilyCompat g).val

theorem proj_apply (i : ι) (x : PolyFamilyLimit g) :
    proj i x = (x : ∀ i, AdjoinRoot (g i)) i :=
  (rfl)

@[simp]
theorem proj_mk (i : ι) (x : ∀ i, AdjoinRoot (g i)) (hx : x ∈ polyFamilyCompat g) :
    proj i (⟨x, hx⟩ : PolyFamilyLimit g) = x i :=
  (rfl)

/-- The transition equation: for `g i ∣ g j`, reducing the coordinate at `j` modulo `g i` gives
the coordinate at `i`. -/
@[simp]
theorem algHomOfDvd_proj {i j : ι} (hij : g i ∣ g j) (x : PolyFamilyLimit g) :
    AdjoinRoot.algHomOfDvd R (g j) (g i) hij (proj j x) = proj i x :=
  mem_polyFamilyCompat.mp x.property i j hij

/-- `algHomOfDvd_proj` as an equality of algebra maps out of the limit. -/
@[simp]
theorem algHomOfDvd_comp_proj {i j : ι} (hij : g i ∣ g j) :
    (AdjoinRoot.algHomOfDvd R (g j) (g i) hij).comp (proj j) = proj (g := g) i :=
  AlgHom.ext (algHomOfDvd_proj hij)

/-- An element of the limit is determined by its projections. -/
@[ext]
theorem ext {x y : PolyFamilyLimit g} (hxy : ∀ i, proj i x = proj i y) : x = y :=
  Subtype.ext (funext hxy)

section liftCompatAlgHom

variable {A : Type*} [Semiring A] [Algebra R A] {φ : ∀ i, A →ₐ[R] AdjoinRoot (g i)}

/-- The universal property of the inverse limit: a family of algebra maps `A → R[X]/(g i)`
compatible with the reductions `AdjoinRoot.algHomOfDvd` induces an algebra map into the limit. -/
noncomputable def liftCompatAlgHom (φ : ∀ i, A →ₐ[R] AdjoinRoot (g i))
    (hφ : ∀ (i j : ι) (hij : g i ∣ g j),
      (AdjoinRoot.algHomOfDvd R (g j) (g i) hij).comp (φ j) = φ i) :
    A →ₐ[R] PolyFamilyLimit g :=
  (AlgHom.pi φ).codRestrict _ fun a ↦
    mem_polyFamilyCompat.mpr fun i j hij ↦ by simpa using DFunLike.congr_fun (hφ i j hij) a

@[simp]
theorem proj_liftCompatAlgHom (hφ) (i : ι) (a : A) :
    proj i (liftCompatAlgHom φ hφ a) = φ i a :=
  (rfl)

theorem proj_comp_liftCompatAlgHom (hφ) (i : ι) :
    (proj i).comp (liftCompatAlgHom φ hφ) = φ i :=
  AlgHom.ext (proj_liftCompatAlgHom hφ i)

/-- Two algebra maps into the limit agree when all their projections agree. -/
theorem algHom_ext {ψ₁ ψ₂ : A →ₐ[R] PolyFamilyLimit g}
    (hψ : ∀ i, (proj i).comp ψ₁ = (proj i).comp ψ₂) : ψ₁ = ψ₂ :=
  AlgHom.ext fun a ↦ ext fun i ↦ DFunLike.congr_fun (hψ i) a

/-- The induced map is the only algebra map with the given projections. -/
theorem liftCompatAlgHom_unique (hφ) (ψ : A →ₐ[R] PolyFamilyLimit g)
    (hψ : ∀ i, (proj i).comp ψ = φ i) : ψ = liftCompatAlgHom φ hφ :=
  algHom_ext fun i ↦ by rw [hψ, proj_comp_liftCompatAlgHom]

end liftCompatAlgHom

variable (g) in
/-- The map `R[X] → lim_i R[X]/(g i)` sending a polynomial to its family of residues. -/
noncomputable def fromPoly : R[X] →ₐ[R] PolyFamilyLimit g :=
  liftCompatAlgHom (fun i ↦ AdjoinRoot.mkₐ (g i)) fun i j hij ↦ AlgHom.ext fun p ↦ by simp

@[simp]
theorem proj_fromPoly (i : ι) (p : R[X]) : proj i (fromPoly g p) = AdjoinRoot.mk (g i) p :=
  (rfl)

theorem proj_comp_fromPoly (i : ι) : (proj i).comp (fromPoly g) = AdjoinRoot.mkₐ (g i) :=
  AlgHom.ext (proj_fromPoly i)

/-- Every projection is surjective: a residue is the projection of the image of any polynomial
representing it. -/
theorem proj_surjective (i : ι) : Function.Surjective (proj (g := g) i) := fun a ↦ by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  exact ⟨fromPoly g p, proj_fromPoly i p⟩

/-! ### The inverse-limit topology -/

/-- The inverse-limit topology on `PolyFamilyLimit g`, induced from the product of the discrete
quotients `R[X]/(g i)`. -/
instance instTopologicalSpace (g : ι → R[X]) : TopologicalSpace (PolyFamilyLimit g) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace ι (fun i ↦ AdjoinRoot (g i)) (fun _ ↦ ⊥))

/-- The topology on `PolyFamilyLimit g` is the initial topology of the projections into the
discrete quotients. -/
theorem topologicalSpace_eq_iInf_induced (g : ι → R[X]) :
    instTopologicalSpace g = ⨅ i, TopologicalSpace.induced (proj (g := g) i) ⊥ := by
  let _ : ∀ i, TopologicalSpace (AdjoinRoot (g i)) := fun _ ↦ ⊥
  rw [instTopologicalSpace, Pi.topologicalSpace, induced_iInf]
  refine iInf_congr fun i ↦ ?_
  rw [induced_compose]
  rfl

/-- Every projection is locally constant. -/
theorem isLocallyConstant_proj (i : ι) :
    IsLocallyConstant (proj (g := g) i : PolyFamilyLimit g → AdjoinRoot (g i)) := by
  let _ : TopologicalSpace (AdjoinRoot (g i)) := ⊥
  have : DiscreteTopology (AdjoinRoot (g i)) := discreteTopology_bot _
  rw [IsLocallyConstant.iff_continuous, continuous_iff_le_induced, topologicalSpace_eq_iInf_induced]
  exact iInf_le _ i

/-- Every projection is continuous, for any topology on the quotient. -/
@[fun_prop, continuity]
theorem continuous_proj (i : ι) [TopologicalSpace (AdjoinRoot (g i))] :
    Continuous (proj (g := g) i) :=
  (isLocallyConstant_proj i).continuous

/-- A map into `PolyFamilyLimit g` is continuous if and only if all its coordinates are locally
constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → PolyFamilyLimit g} :
    Continuous f ↔ ∀ i, IsLocallyConstant (proj i ∘ f) := by
  rw [topologicalSpace_eq_iInf_induced, continuous_iInf_rng]
  refine forall_congr' fun i ↦ ?_
  let _ : TopologicalSpace (AdjoinRoot (g i)) := ⊥
  have : DiscreteTopology (AdjoinRoot (g i)) := discreteTopology_bot _
  rw [continuous_induced_rng, IsLocallyConstant.iff_continuous]

instance (g : ι → R[X]) : IsTopologicalRing (PolyFamilyLimit g) := by
  let _ : ∀ i, TopologicalSpace (AdjoinRoot (g i)) := fun _ ↦ ⊥
  have : ∀ i, DiscreteTopology (AdjoinRoot (g i)) := fun _ ↦ discreteTopology_bot _
  exact Subring.instIsTopologicalRing (polyFamilyCompat g).toSubring

instance (g : ι → R[X]) : T2Space (PolyFamilyLimit g) := by
  let _ : ∀ i, TopologicalSpace (AdjoinRoot (g i)) := fun _ ↦ ⊥
  have : ∀ i, DiscreteTopology (AdjoinRoot (g i)) := fun _ ↦ discreteTopology_bot _
  exact inferInstance

/-! ### Reduction from a dominating coordinate -/

/-- For a directed family, reducing a coordinate `x i` modulo a divisor `p ∣ g i` does not depend
on the choice of `i`. -/
theorem algHomOfDvd_comp_proj_eq (hg : Directed (· ∣ ·) g) {p : R[X]} {i i' : ι}
    (hi : p ∣ g i) (hi' : p ∣ g i') :
    (AdjoinRoot.algHomOfDvd R (g i) p hi).comp (proj i) =
      (AdjoinRoot.algHomOfDvd R (g i') p hi').comp (proj i') := by
  obtain ⟨j, hij, hi'j⟩ := hg i i'
  rw [← algHomOfDvd_comp_proj hij, ← algHomOfDvd_comp_proj hi'j, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, AdjoinRoot.algHomOfDvd_comp_algHomOfDvd,
    AdjoinRoot.algHomOfDvd_comp_algHomOfDvd]

/-- For a polynomial `p` dividing some `g i`, the reduction `lim_i R[X]/(g i) → R[X]/(p)` of the
coordinate at a chosen such `i`. When `g` is directed, every such `i` gives the same map
(`TauCeti.PolyFamilyLimit.projOfDvd_eq`). -/
noncomputable def projOfDvd {p : R[X]} (hp : ∃ i, p ∣ g i) :
    PolyFamilyLimit g →ₐ[R] AdjoinRoot p :=
  (AdjoinRoot.algHomOfDvd R (g hp.choose) p hp.choose_spec).comp (proj hp.choose)

/-- `projOfDvd` reduces the coordinate at any `i` with `p ∣ g i`. -/
theorem projOfDvd_eq (hg : Directed (· ∣ ·) g) {p : R[X]} {i : ι} (hi : p ∣ g i) :
    projOfDvd ⟨i, hi⟩ = (AdjoinRoot.algHomOfDvd R (g i) p hi).comp (proj i) :=
  algHomOfDvd_comp_proj_eq hg _ hi

theorem projOfDvd_apply (hg : Directed (· ∣ ·) g) {p : R[X]} {i : ι} (hi : p ∣ g i)
    (x : PolyFamilyLimit g) :
    projOfDvd ⟨i, hi⟩ x = AdjoinRoot.algHomOfDvd R (g i) p hi (proj i x) := by
  rw [projOfDvd_eq hg hi, AlgHom.comp_apply]

/-- On a member of the family, `projOfDvd` is the projection. -/
@[simp]
theorem projOfDvd_self (hg : Directed (· ∣ ·) g) (i : ι) :
    projOfDvd ⟨i, dvd_refl (g i)⟩ = proj i := by
  rw [projOfDvd_eq hg (dvd_refl (g i)), AdjoinRoot.algHomOfDvd_self, AlgHom.id_comp]

@[simp]
theorem projOfDvd_fromPoly {p : R[X]} (hp : ∃ i, p ∣ g i)
    (q : R[X]) : projOfDvd hp (fromPoly g q) = AdjoinRoot.mk p q := by
  rw [projOfDvd, AlgHom.comp_apply, proj_fromPoly, AdjoinRoot.algHomOfDvd_mk]

/-- Reducing `projOfDvd` further modulo `p' ∣ p` is `projOfDvd` for `p'`. -/
theorem algHomOfDvd_comp_projOfDvd (hg : Directed (· ∣ ·) g) {p p' : R[X]} (hp : ∃ i, p ∣ g i)
    (hp' : p' ∣ p) :
    (AdjoinRoot.algHomOfDvd R p p' hp').comp (projOfDvd hp) =
      projOfDvd (hp.imp fun _ hi ↦ hp'.trans hi) := by
  obtain ⟨i, hi⟩ := hp
  rw [projOfDvd_eq hg hi, projOfDvd_eq hg (hp'.trans hi), ← AlgHom.comp_assoc,
    AdjoinRoot.algHomOfDvd_comp_algHomOfDvd]

theorem isLocallyConstant_projOfDvd {p : R[X]} (hp : ∃ i, p ∣ g i) :
    IsLocallyConstant (projOfDvd hp : PolyFamilyLimit g → AdjoinRoot p) :=
  (isLocallyConstant_proj _).comp _

/-! ### Comparison of cofinal families -/

/-- For a directed family `g` dominating `h` (every `h j` divides some `g i`), the algebra map
`lim_i R[X]/(g i) → lim_j R[X]/(h j)` induced by the identity of `R[X]`: its coordinate at `j` is
the reduction of any coordinate `x i` with `h j ∣ g i`. -/
noncomputable def reduce (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) :
    PolyFamilyLimit g →ₐ[R] PolyFamilyLimit h :=
  liftCompatAlgHom (fun j ↦ projOfDvd (hhg j)) fun _ _ hjj' ↦
    algHomOfDvd_comp_projOfDvd hg _ hjj'

theorem proj_comp_reduce (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) (j : κ) :
    (proj j).comp (reduce hg hhg) = projOfDvd (hhg j) :=
  proj_comp_liftCompatAlgHom _ j

/-- The coordinate equation: the coordinate at `j` of the comparison map is the reduction of the
coordinate at any `i` with `h j ∣ g i`. -/
theorem proj_reduce (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) {j : κ} {i : ι}
    (hji : h j ∣ g i) (x : PolyFamilyLimit g) :
    proj j (reduce hg hhg x) = AdjoinRoot.algHomOfDvd R (g i) (h j) hji (proj i x) :=
  projOfDvd_apply hg hji x

/-- The comparison map extends the identity of `R[X]`. -/
@[simp]
theorem reduce_fromPoly (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) (p : R[X]) :
    reduce hg hhg (fromPoly g p) = fromPoly h p :=
  ext fun j ↦ by rw [← AlgHom.comp_apply, proj_comp_reduce, projOfDvd_fromPoly, proj_fromPoly]

@[simp]
theorem reduce_comp_fromPoly (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) :
    (reduce hg hhg).comp (fromPoly g) = fromPoly h :=
  AlgHom.ext (reduce_fromPoly hg hhg)

/-- The comparison of a directed family with itself is the identity. -/
@[simp]
theorem reduce_eq_id (hg : Directed (· ∣ ·) g) (hgg : ∀ i, ∃ i', g i ∣ g i') :
    reduce hg hgg = AlgHom.id R (PolyFamilyLimit g) :=
  AlgHom.ext fun x ↦ ext fun i ↦ by
    rw [proj_reduce hg hgg (dvd_refl (g i)), AdjoinRoot.algHomOfDvd_self, AlgHom.id_apply,
      AlgHom.id_apply]

/-- Comparison maps compose. -/
@[simp]
theorem reduce_comp_reduce (hg : Directed (· ∣ ·) g) (hh : Directed (· ∣ ·) h)
    (hhg : ∀ j, ∃ i, h j ∣ g i) (hkh : ∀ l, ∃ j, k l ∣ h j) (hkg : ∀ l, ∃ i, k l ∣ g i) :
    (reduce hh hkh).comp (reduce hg hhg) = reduce hg hkg :=
  AlgHom.ext fun x ↦ ext fun l ↦ by
    obtain ⟨j, hlj⟩ := hkh l
    obtain ⟨i, hji⟩ := hhg j
    rw [AlgHom.comp_apply, proj_reduce hh hkh hlj, proj_reduce hg hhg hji,
      AdjoinRoot.algHomOfDvd_algHomOfDvd, proj_reduce hg hkg (hlj.trans hji)]

@[simp]
theorem reduce_reduce (hg : Directed (· ∣ ·) g) (hh : Directed (· ∣ ·) h)
    (hhg : ∀ j, ∃ i, h j ∣ g i) (hkh : ∀ l, ∃ j, k l ∣ h j) (hkg : ∀ l, ∃ i, k l ∣ g i)
    (x : PolyFamilyLimit g) :
    reduce hh hkh (reduce hg hhg x) = reduce hg hkg x :=
  AlgHom.congr_fun (reduce_comp_reduce hg hh hhg hkh hkg) x

/-- The comparison map is continuous. -/
@[fun_prop, continuity]
theorem continuous_reduce (hg : Directed (· ∣ ·) g) (hhg : ∀ j, ∃ i, h j ∣ g i) :
    Continuous (reduce hg hhg) :=
  continuous_iff.mpr fun j ↦ by
    rw [← AlgHom.coe_comp, proj_comp_reduce]
    exact isLocallyConstant_projOfDvd (hhg j)

/-- **Cofinal change of presentation.** Two directed, mutually cofinal families of polynomials
have isomorphic limits, as topological `R`-algebras, by the isomorphism induced by the identity
of `R[X]`. -/
noncomputable def cofinalEquiv (hg : Directed (· ∣ ·) g) (hh : Directed (· ∣ ·) h)
    (hhg : ∀ j, ∃ i, h j ∣ g i) (hgh : ∀ i, ∃ j, g i ∣ h j) :
    PolyFamilyLimit g ≃A[R] PolyFamilyLimit h where
  toAlgEquiv := AlgEquiv.ofAlgHom (reduce hg hhg) (reduce hh hgh)
    (by rw [reduce_comp_reduce hh hg hgh hhg fun j ↦ ⟨j, dvd_refl (h j)⟩, reduce_eq_id])
    (by rw [reduce_comp_reduce hg hh hhg hgh fun i ↦ ⟨i, dvd_refl (g i)⟩, reduce_eq_id])
  continuous_toFun := continuous_reduce hg hhg
  continuous_invFun := continuous_reduce hh hgh

variable (hg : Directed (· ∣ ·) g) (hh : Directed (· ∣ ·) h) (hhg : ∀ j, ∃ i, h j ∣ g i)
  (hgh : ∀ i, ∃ j, g i ∣ h j)

@[simp]
theorem coe_cofinalEquiv : ⇑(cofinalEquiv hg hh hhg hgh) = reduce hg hhg :=
  (rfl)

theorem cofinalEquiv_apply (x : PolyFamilyLimit g) :
    cofinalEquiv hg hh hhg hgh x = reduce hg hhg x :=
  (rfl)

/-- The inverse of a cofinal equivalence is the cofinal equivalence in the other direction. -/
@[simp]
theorem cofinalEquiv_symm :
    (cofinalEquiv hg hh hhg hgh).symm = cofinalEquiv hh hg hgh hhg :=
  (rfl)

/-- The coordinate equation of a cofinal equivalence. -/
theorem proj_cofinalEquiv {j : κ} {i : ι} (hji : h j ∣ g i) (x : PolyFamilyLimit g) :
    proj j (cofinalEquiv hg hh hhg hgh x) =
      AdjoinRoot.algHomOfDvd R (g i) (h j) hji (proj i x) :=
  proj_reduce hg hhg hji x

theorem cofinalEquiv_fromPoly (p : R[X]) :
    cofinalEquiv hg hh hhg hgh (fromPoly g p) = fromPoly h p :=
  reduce_fromPoly hg hhg p

/-- **Transitivity of cofinal replacement.** -/
@[simp]
theorem cofinalEquiv_trans (hk : Directed (· ∣ ·) k) (hkh : ∀ l, ∃ j, k l ∣ h j)
    (hhk : ∀ j, ∃ l, h j ∣ k l) (hkg : ∀ l, ∃ i, k l ∣ g i) (hgk : ∀ i, ∃ l, g i ∣ k l) :
    (cofinalEquiv hg hh hhg hgh).trans (cofinalEquiv hh hk hkh hhk) =
      cofinalEquiv hg hk hkg hgk :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ reduce_reduce hg hh hhg hkh hkg x

end PolyFamilyLimit

/-! ### Examples -/

/-- In the limit along the powers of `q - 1` over `ℤ`, residue `1` modulo `(q - 1) ^ 2` forces
residue `1`, not `0`, modulo `q - 1`: the transitions constrain the family. -/
example (x : PolyFamilyLimit fun k : ℕ ↦ (X - 1 : ℤ[X]) ^ k)
    (h2 : PolyFamilyLimit.proj 2 x = 1) : PolyFamilyLimit.proj 1 x ≠ 0 := by
  have : Nontrivial (AdjoinRoot ((X - 1 : ℤ[X]) ^ 1)) :=
    AdjoinRoot.nontrivial _ (by rw [pow_one, ← C_1, degree_X_sub_C]; exact one_ne_zero)
  rw [← PolyFamilyLimit.algHomOfDvd_proj (pow_dvd_pow _ (by norm_num : 1 ≤ 2)) x, h2, map_one]
  exact one_ne_zero

end TauCeti
