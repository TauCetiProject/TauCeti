/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.HopfAlgebra.WeilRestriction
public import TauCeti.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.PowerSeries.Jet
public import TauCeti.Algebra.HopfAlgebra.DirectLimit
import TauCeti.Algebra.Coalgebra.Convolution
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# Jet groups and the positive loop group

Let `H` be a commutative Hopf algebra over a commutative ring `k`, the coordinate ring of an affine
group `G`. For a commutative `k`-algebra `R`, the positive loop group is `L⁺G(R) = G(R⟦X⟧)`, the
convolution group `WithConv (H →ₐ[k] R⟦X⟧)` of points of `H` in `R⟦X⟧`. This file presents it as
the inverse limit of the jet groups, as affine group functors.

The **jet group of level `N`** is the affine group `J_N G = Res_{k[X]/(X ^ N) / k} G`, the Weil
restriction along `k[X]/(X ^ N)` of the base change of `G`. Its coordinate ring is the commutative
Hopf `k`-algebra `jetHopfAlgebra k H N`, and its points are `J_N G(R) = G(R[X]/(X ^ N))`
(`jetPointsMulEquiv`). Truncation `R[X]/(X ^ (N + 1)) → R[X]/(X ^ N)` is induced by the Hopf
algebra map `jetTruncation k H N`, and taking jets of coefficients gives the projections
`jetProjection N : G(R⟦X⟧) → J_N G(R)`. They identify `L⁺G(R)` with the group `jetLimit k H R` of
compatible sequences of jets (`positiveLoopJetLimitMulEquiv`), naturally in `R`, and the kernel of
the `N`-th projection is the congruence subgroup `K_N(R)` of level `(X ^ N)`.

As an affine group, `L⁺G` is represented by the directed colimit `positiveLoopHopfAlgebra k H` of
the jet Hopf algebras along the truncations, a commutative Hopf `k`-algebra
(`DirectLimit.instHopfAlgebra`): its points over `R` are `L⁺G(R)`
(`positiveLoopPointsMulEquiv`), naturally in `R` and compatibly with the projections to the jet
groups. For the trivial group it is `k` (`positiveLoopHopfAlgebraSelfAlgEquiv`).

Everything holds for every commutative `k`-algebra `R`, nonreduced ones included, and over any
commutative ring `k`. When `H` is of finite type or smooth over `k`, so is each
`jetHopfAlgebra k H N`, by the instances `WeilRestriction.instFiniteType` and
`WeilRestriction.instSmooth`; so for `H` of finite type the jet groups are algebraic groups and
this is the presentation of `L⁺G` as a proalgebraic group.

## Main definitions

* `TauCeti.HopfAlgebra.jetHopfAlgebra k H N`: the coordinate Hopf algebra of the jet group of
  level `N`.
* `TauCeti.HopfAlgebra.jetPointsMulEquiv`: the group isomorphism `J_N G(R) ≃* G(R[X]/(X ^ N))`.
* `TauCeti.HopfAlgebra.jetTruncation k H N`: the Hopf algebra map inducing the truncation
  `J_(N+1) G → J_N G`.
* `TauCeti.HopfAlgebra.jetProjection`: the projection `L⁺G(R) → J_N G(R)`.
* `TauCeti.HopfAlgebra.jetLimit`: the inverse limit of the groups `J_N G(R)` along the
  truncations.
* `TauCeti.HopfAlgebra.positiveLoopJetLimitMulEquiv`: the isomorphism of `L⁺G(R)` with that
  inverse limit.
* `TauCeti.HopfAlgebra.positiveLoopHopfAlgebra`: the coordinate Hopf algebra of `L⁺G`, the
  directed colimit of the jet Hopf algebras.
* `TauCeti.HopfAlgebra.positiveLoopPointsMulEquiv`: its points are the positive loops.
* `TauCeti.HopfAlgebra.positiveLoopHopfAlgebraSelfAlgEquiv`: for the trivial group it is `k`.
* `TauCeti.HopfAlgebra.positiveLoopEvalZero` and `TauCeti.HopfAlgebra.constantPositiveLoop`:
  evaluation `L⁺G(R) → G(R)` at `X = 0` and the constant loops, a section of it.

## Main results

* `TauCeti.HopfAlgebra.jetPointsMulEquiv_mapDomain_jetTruncation`: on points, `jetTruncation` is
  truncation of the coefficients.
* `TauCeti.HopfAlgebra.ker_jetProjection`: the kernel of the `N`-th projection is the congruence
  subgroup `K_N(R)` of level `(X ^ N)`.
* `TauCeti.HopfAlgebra.positiveLoopJetLimitMulEquiv_naturality`: the isomorphism with the inverse
  limit is natural in `R`.
* `TauCeti.HopfAlgebra.ker_positiveLoopEvalZero`: the kernel of evaluation at `X = 0` is `K_1(R)`.
* `TauCeti.HopfAlgebra.jetProjection_positiveLoopPointsMulEquiv` and
  `TauCeti.HopfAlgebra.positiveLoopPointsMulEquiv_naturality`: the points of
  `positiveLoopHopfAlgebra k H` are compatible with the projections to the jet groups and natural
  in `R`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Studies in Advanced
  Mathematics 103 (2007), §1.3.1.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open WithConv
open scoped Polynomial PowerSeries TensorProduct

namespace TauCeti.HopfAlgebra

variable (k : Type*) [CommRing k] (H : Type*) [CommRing H] [_root_.HopfAlgebra k H]

/-- **The jet group of level `N`.** The coordinate Hopf algebra of the affine group
`J_N G = Res_{k[X]/(X ^ N) / k} G`, the Weil restriction along the truncated polynomial algebra
`k[X]/(X ^ N)` of the base change of `G = Spec H`. Its points over `R` are `G(R[X]/(X ^ N))`
(`jetPointsMulEquiv`). -/
abbrev jetHopfAlgebra (N : ℕ) : Type _ :=
  Algebra.WeilRestriction k (AdjoinRoot (Polynomial.X ^ N : k[X]))
    (AdjoinRoot (Polynomial.X ^ N : k[X]) ⊗[k] H)

section Points

variable (R : Type*) [CommRing R] [Algebra k R]

/-- **The points of the jet group.** The group isomorphism `J_N G(R) ≃* G(R[X]/(X ^ N))`: the
points of the Weil restriction (`WeilRestriction.pointsMulEquiv`) are the points of the base
change of `G` in `k[X]/(X ^ N) ⊗[k] R`, which are points of `G` in that algebra
(`AlgHom.baseChangePointsMulEquiv`), and `k[X]/(X ^ N) ⊗[k] R = R[X]/(X ^ N)`
(`AdjoinRoot.tensorXPowAlgEquiv`). -/
noncomputable def jetPointsMulEquiv (N : ℕ) :
    WithConv (jetHopfAlgebra k H N →ₐ[k] R) ≃*
      WithConv (H →ₐ[k] AdjoinRoot (Polynomial.X ^ N : R[X])) :=
  (Algebra.WeilRestriction.pointsMulEquiv k _ _ R).trans <|
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := AdjoinRoot (Polynomial.X ^ N : k[X])) (A := H)
      (R := AdjoinRoot (Polynomial.X ^ N : k[X]) ⊗[k] R)).symm.trans <|
      MonoidHom.toMulEquiv (AlgHom.mapValue (AdjoinRoot.tensorXPowAlgEquiv k R N).toAlgHom)
        (AlgHom.mapValue (AdjoinRoot.tensorXPowAlgEquiv k R N).symm.toAlgHom)
        (by rw [← AlgHom.mapValue_comp, AlgEquiv.symm_comp, AlgHom.mapValue_id])
        (by rw [← AlgHom.mapValue_comp, AlgEquiv.comp_symm, AlgHom.mapValue_id])

variable {k H R}

/-- The point of `G(R[X]/(X ^ N))` attached to a point of the jet group takes `h` to the image of
`1 ⊗ h` under the point of the base change classified by `WeilRestriction.homEquiv`. -/
@[simp]
theorem jetPointsMulEquiv_apply_apply {N : ℕ} (f : WithConv (jetHopfAlgebra k H N →ₐ[k] R))
    (h : H) :
    (jetPointsMulEquiv k H R N f).ofConv h =
      AdjoinRoot.tensorXPowAlgEquiv k R N
        (Algebra.WeilRestriction.homEquiv k _ _ R f.ofConv (1 ⊗ₜ h)) := by
  simp [jetPointsMulEquiv]

/-- **Naturality of `jetPointsMulEquiv` in `R`.** A map `φ : R →ₐ[k] S` acts on the points of
the jet group by post-composition, and on `G(R[X]/(X ^ N))` through the coefficientwise map
`R[X]/(X ^ N) → S[X]/(X ^ N)`. -/
theorem jetPointsMulEquiv_naturality {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S)
    {N : ℕ} (f : WithConv (jetHopfAlgebra k H N →ₐ[k] R)) :
    jetPointsMulEquiv k H S N (AlgHom.mapValue φ f) =
      AlgHom.mapValue (AdjoinRoot.mapAlgHom φ (Polynomial.X ^ N) (Polynomial.X ^ N) (by simp))
        (jetPointsMulEquiv k H R N f) := by
  have hφ : ((Algebra.TensorProduct.lTensor (S := AdjoinRoot (Polynomial.X ^ N : k[X]))
      (AdjoinRoot (Polynomial.X ^ N : k[X])) φ).restrictScalars k) =
        Algebra.TensorProduct.map (AlgHom.id k _) φ := by
    ext <;> simp
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp only [jetPointsMulEquiv_apply_apply, AlgHom.mapValue_apply, ofConv_toConv,
    Algebra.WeilRestriction.homEquiv_comp, AlgHom.comp_apply]
  have key := DFunLike.congr_fun (AdjoinRoot.tensorXPowAlgEquiv_comp_map (N := N) φ)
    (Algebra.WeilRestriction.homEquiv k _ _ R f.ofConv (1 ⊗ₜ h))
  rw [← hφ] at key
  exact key

end Points

section Truncation

variable {T : Type*} [CommRing T] [Algebra k T] (N : ℕ)

-- The algebra map of the truncation `J_(N+1) G → J_N G`: by the Yoneda lemma, the map classifying
-- the truncation of the universal point of `J_(N+1) G`.
private noncomputable def jetTruncationAlgHom :
    jetHopfAlgebra k H N →ₐ[k] jetHopfAlgebra k H (N + 1) :=
  ((jetPointsMulEquiv k H (jetHopfAlgebra k H (N + 1)) N).symm
    (AlgHom.mapValue ((AdjoinRoot.algHomOfDvd (jetHopfAlgebra k H (N + 1))
        (Polynomial.X ^ (N + 1)) (Polynomial.X ^ N)
        (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k)
      (jetPointsMulEquiv k H _ (N + 1) (toConv (AlgHom.id k _))))).ofConv

variable {k H}

-- Pre-composition with `jetTruncationAlgHom` is truncation of the coefficients.
private theorem jetPointsMulEquiv_comp_jetTruncationAlgHom
    (f : jetHopfAlgebra k H (N + 1) →ₐ[k] T) :
    jetPointsMulEquiv k H T N (toConv (f.comp (jetTruncationAlgHom k H N))) =
      AlgHom.mapValue ((AdjoinRoot.algHomOfDvd T (Polynomial.X ^ (N + 1) : T[X])
          (Polynomial.X ^ N) (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k)
        (jetPointsMulEquiv k H T (N + 1) (toConv f)) := by
  have hf (M : ℕ) (g : jetHopfAlgebra k H M →ₐ[k] jetHopfAlgebra k H (N + 1)) :
      toConv (f.comp g) = AlgHom.mapValue f (toConv g) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv]
  -- truncation commutes with the coefficientwise map induced by `f`
  have hsq : (AdjoinRoot.mapAlgHom f (Polynomial.X ^ N) (Polynomial.X ^ N) (by simp)).comp
      ((AdjoinRoot.algHomOfDvd (jetHopfAlgebra k H (N + 1)) (Polynomial.X ^ (N + 1))
        (Polynomial.X ^ N) (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k) =
      ((AdjoinRoot.algHomOfDvd T (Polynomial.X ^ (N + 1) : T[X]) (Polynomial.X ^ N)
        (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k).comp
        (AdjoinRoot.mapAlgHom f (Polynomial.X ^ (N + 1)) (Polynomial.X ^ (N + 1)) (by simp)) :=
    AdjoinRoot.algHom_ext' (AlgHom.ext fun x ↦ by simp [AdjoinRoot.algHomOfDvd]) (by simp)
  rw [hf, jetPointsMulEquiv_naturality, jetTruncationAlgHom, toConv_ofConv,
    MulEquiv.apply_symm_apply, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, hsq,
    AlgHom.mapValue_comp, MonoidHom.comp_apply, ← jetPointsMulEquiv_naturality, ← hf,
    AlgHom.comp_id]

-- Pre-composition with `jetTruncationAlgHom` is multiplicative on points.
private theorem toConv_comp_jetTruncationAlgHom_mul
    {f g : WithConv (jetHopfAlgebra k H (N + 1) →ₐ[k] T)} :
    toConv ((f * g).ofConv.comp (jetTruncationAlgHom k H N)) =
      toConv (f.ofConv.comp (jetTruncationAlgHom k H N)) *
        toConv (g.ofConv.comp (jetTruncationAlgHom k H N)) :=
  (jetPointsMulEquiv k H T N).injective <| by
    rw [map_mul, jetPointsMulEquiv_comp_jetTruncationAlgHom,
      jetPointsMulEquiv_comp_jetTruncationAlgHom, jetPointsMulEquiv_comp_jetTruncationAlgHom,
      toConv_ofConv, toConv_ofConv, toConv_ofConv, map_mul, map_mul]

variable (k H)

/-- **Truncation of jets.** The Hopf algebra map `jetHopfAlgebra k H N → jetHopfAlgebra k H (N + 1)`
of the truncation homomorphism `J_(N+1) G → J_N G`; on points it is the map
`G(R[X]/(X ^ (N + 1))) → G(R[X]/(X ^ N))` induced by truncation
(`jetPointsMulEquiv_mapDomain_jetTruncation`). -/
noncomputable def jetTruncation : jetHopfAlgebra k H N →ₐc[k] jetHopfAlgebra k H (N + 1) :=
  .ofAlgHom (jetTruncationAlgHom k H N)
    (by
      -- both counits are identity points, and truncation preserves the identity
      refine WithConv.toConv_injective ((jetPointsMulEquiv k H k N).injective ?_)
      simp only [← Bialgebra.ofConv_one_eq_counitAlgHom, jetPointsMulEquiv_comp_jetTruncationAlgHom,
        toConv_ofConv, map_one])
    (AlgHom.map_comp_comulAlgHom_of_mul _ fun _ _ ↦ toConv_comp_jetTruncationAlgHom_mul N)

variable {k H}

/-- **`jetTruncation` on points.** Under `jetPointsMulEquiv`, pre-composition with
`jetTruncation k H N` is the map `G(T[X]/(X ^ (N + 1))) → G(T[X]/(X ^ N))` induced by truncation. -/
theorem jetPointsMulEquiv_mapDomain_jetTruncation
    (f : WithConv (jetHopfAlgebra k H (N + 1) →ₐ[k] T)) :
    jetPointsMulEquiv k H T N (BialgHom.mapDomain (jetTruncation k H N) f) =
      AlgHom.mapValue ((AdjoinRoot.algHomOfDvd T (Polynomial.X ^ (N + 1) : T[X])
          (Polynomial.X ^ N) (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k)
        (jetPointsMulEquiv k H T (N + 1) f) := by
  rw [BialgHom.mapDomain_apply]
  -- the algebra map underlying `jetTruncation` is `jetTruncationAlgHom` by construction
  exact jetPointsMulEquiv_comp_jetTruncationAlgHom N f.ofConv

end Truncation

section Limit

variable (R : Type*) [CommRing R] [Algebra k R]

/-- **The projection of the positive loop group to the jet group of level `N`.** The homomorphism
`L⁺G(R) = G(R⟦X⟧) → J_N G(R)` taking the `N`-jets `R⟦X⟧ → R[X]/(X ^ N)` of the values of a
point. -/
noncomputable def jetProjection (N : ℕ) :
    WithConv (H →ₐ[k] R⟦X⟧) →* WithConv (jetHopfAlgebra k H N →ₐ[k] R) :=
  (jetPointsMulEquiv k H R N).symm.toMonoidHom.comp
    (AlgHom.mapValue ((PowerSeries.jet R N).restrictScalars k))

variable {k H R}

/-- Under `jetPointsMulEquiv`, the `N`-th projection takes the `N`-jets of the values. -/
@[simp]
theorem jetPointsMulEquiv_jetProjection {N : ℕ} (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    jetPointsMulEquiv k H R N (jetProjection k H R N g) =
      AlgHom.mapValue ((PowerSeries.jet R N).restrictScalars k) g := by
  rw [jetProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

/-- The projections are compatible with the truncations `J_(N+1) G → J_N G`. -/
theorem mapDomain_jetTruncation_jetProjection {N : ℕ} (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    BialgHom.mapDomain (jetTruncation k H N) (jetProjection k H R (N + 1) g) =
      jetProjection k H R N g := by
  refine (jetPointsMulEquiv k H R N).injective ?_
  rw [jetPointsMulEquiv_mapDomain_jetTruncation, jetPointsMulEquiv_jetProjection,
    jetPointsMulEquiv_jetProjection, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
  congr 2
  exact AlgHom.ext fun f ↦ PowerSeries.algHomOfDvd_jet N.le_succ f

/-- **The kernel of the `N`-th projection is the congruence subgroup `K_N(R)`** of level
`(X ^ N)`: a loop has trivial `N`-jet exactly when it is the identity modulo `X ^ N`. -/
theorem ker_jetProjection (N : ℕ) :
    (jetProjection k H R N).ker = congruenceSubgroup k H (Ideal.span {PowerSeries.X ^ N}) := by
  have hker : RingHom.ker ((PowerSeries.jet R N).restrictScalars k) = RingHom.ker
      (PowerSeries.jet R N) := by
    ext f
    rw [RingHom.mem_ker, RingHom.mem_ker, AlgHom.restrictScalars_apply]
  rw [← PowerSeries.ker_jet, ← hker, ← ker_mapValue_eq_congruenceSubgroup]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, jetProjection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_one]⟩
  simpa using congrArg (jetPointsMulEquiv k H R N) h

/-- **Naturality of the projections in `R`.** For `φ : R →ₐ[k] S`, projecting the coefficientwise
image of a loop is mapping its projection along `φ`. -/
theorem jetProjection_naturality {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) {N : ℕ}
    (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    jetProjection k H S N (AlgHom.mapValue (PowerSeries.mapAlgHom φ) g) =
      AlgHom.mapValue φ (jetProjection k H R N g) := by
  refine (jetPointsMulEquiv k H S N).injective ?_
  rw [jetPointsMulEquiv_jetProjection, jetPointsMulEquiv_naturality,
    jetPointsMulEquiv_jetProjection, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp,
    ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
  congr 2
  refine AlgHom.ext fun f ↦ ?_
  simpa [PowerSeries.mapAlgHom_apply] using (PowerSeries.map_jet (N := N) φ.toRingHom f).symm

variable (k H R)

/-- **The inverse limit of the jet groups.** The subgroup of `∏ N, J_N G(R)` of sequences
compatible with the truncations `J_(N+1) G(R) → J_N G(R)`. -/
def jetLimit : Subgroup (∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] R)) where
  carrier := {g | ∀ N, BialgHom.mapDomain (jetTruncation k H N) (g (N + 1)) = g N}
  mul_mem' {a b} ha hb N := by rw [Pi.mul_apply, map_mul, ha N, hb N, Pi.mul_apply]
  one_mem' N := map_one _
  inv_mem' {a} ha N := by rw [Pi.inv_apply, map_inv, ha N, Pi.inv_apply]

variable {k H R}

/-- A sequence of jets lies in the inverse limit exactly when each term is the truncation of the
next. -/
@[simp]
theorem mem_jetLimit_iff {g : ∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] R)} :
    g ∈ jetLimit k H R ↔ ∀ N, BialgHom.mapDomain (jetTruncation k H N) (g (N + 1)) = g N :=
  Iff.rfl

-- The projections of a loop determine it.
private theorem jetProjection_injective {g g' : WithConv (H →ₐ[k] R⟦X⟧)}
    (h : ∀ N, jetProjection k H R N g = jetProjection k H R N g') : g = g' := by
  refine WithConv.ofConv_injective (AlgHom.ext fun x ↦ PowerSeries.eq_of_forall_jet_eq fun N ↦ ?_)
  have hN := congrArg (jetPointsMulEquiv k H R N) (h N)
  rw [jetPointsMulEquiv_jetProjection, jetPointsMulEquiv_jetProjection] at hN
  simpa using congrArg (fun p ↦ p.ofConv x) hN

-- Every compatible sequence of jets is the sequence of projections of a loop.
private theorem exists_forall_jetProjection_eq {c : ∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] R)}
    (hc : c ∈ jetLimit k H R) : ∃ g, ∀ N, jetProjection k H R N g = c N := by
  obtain ⟨ψ, hψ⟩ := PowerSeries.exists_algHom_forall_jet_comp_eq
    (fun N ↦ (jetPointsMulEquiv k H R N (c N)).ofConv) fun N ↦ by
      rw [← hc N, jetPointsMulEquiv_mapDomain_jetTruncation, AlgHom.mapValue_apply,
        ofConv_toConv]
  refine ⟨toConv ψ, fun N ↦ (jetPointsMulEquiv k H R N).injective ?_⟩
  rw [jetPointsMulEquiv_jetProjection, AlgHom.mapValue_apply, ofConv_toConv, hψ, toConv_ofConv]

variable (k H R)

/-- **The positive loop group is the inverse limit of the jet groups.** The projections
`L⁺G(R) → J_N G(R)` identify `L⁺G(R) = G(R⟦X⟧)` with the group of compatible sequences of jets;
this is natural in `R` (`positiveLoopJetLimitMulEquiv_naturality`). -/
noncomputable def positiveLoopJetLimitMulEquiv :
    WithConv (H →ₐ[k] R⟦X⟧) ≃* jetLimit k H R :=
  MulEquiv.ofBijective
    ((MonoidHom.pi fun N ↦ jetProjection k H R N).codRestrict (jetLimit k H R) fun g _ ↦
      mapDomain_jetTruncation_jetProjection g)
    ⟨fun _ _ h ↦ jetProjection_injective fun N ↦ congr_fun (congrArg Subtype.val h) N,
      fun c ↦ (exists_forall_jetProjection_eq c.property).imp fun _ hg ↦ Subtype.ext (funext hg)⟩

variable {k H R}

/-- The `N`-th term of the sequence of jets of a loop is its `N`-th projection. -/
@[simp]
theorem positiveLoopJetLimitMulEquiv_apply (g : WithConv (H →ₐ[k] R⟦X⟧)) (N : ℕ) :
    (↑(positiveLoopJetLimitMulEquiv k H R g) : ∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] R)) N =
      jetProjection k H R N g := (rfl)

/-- **Naturality of `positiveLoopJetLimitMulEquiv` in `R`.** For `φ : R →ₐ[k] S`, the jets of
the coefficientwise image of a loop are the images of its jets. -/
theorem positiveLoopJetLimitMulEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (φ : R →ₐ[k] S) (g : WithConv (H →ₐ[k] R⟦X⟧)) (N : ℕ) :
    (↑(positiveLoopJetLimitMulEquiv k H S (AlgHom.mapValue (PowerSeries.mapAlgHom φ) g)) :
      ∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] S)) N =
        AlgHom.mapValue φ
          ((↑(positiveLoopJetLimitMulEquiv k H R g) :
            ∀ N, WithConv (jetHopfAlgebra k H N →ₐ[k] R)) N) := by
  rw [positiveLoopJetLimitMulEquiv_apply, positiveLoopJetLimitMulEquiv_apply,
    jetProjection_naturality]

end Limit

section EvalZero

variable (R : Type*) [CommRing R] [Algebra k R]

/-- **Evaluation of loops at `X = 0`**, the homomorphism `L⁺G(R) = G(R⟦X⟧) → G(R)` induced by the
constant coefficient. The constant loops are a section of it
(`positiveLoopEvalZero_constantPositiveLoop`), and its kernel is `K_1(R)`
(`ker_positiveLoopEvalZero`). -/
noncomputable def positiveLoopEvalZero : WithConv (H →ₐ[k] R⟦X⟧) →* WithConv (H →ₐ[k] R) :=
  AlgHom.mapValue (PowerSeries.constantCoeffAlgHom k)

/-- **The constant loops**, the homomorphism `G(R) → L⁺G(R) = G(R⟦X⟧)` induced by the inclusion
of constant power series. -/
noncomputable def constantPositiveLoop : WithConv (H →ₐ[k] R) →* WithConv (H →ₐ[k] R⟦X⟧) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom k R R⟦X⟧)

variable {k H R}

/-- Evaluating a loop at `X = 0` takes the constant coefficient of each of its values. -/
@[simp]
theorem ofConv_positiveLoopEvalZero_apply (g : WithConv (H →ₐ[k] R⟦X⟧)) (h : H) :
    (positiveLoopEvalZero k H R g).ofConv h = PowerSeries.constantCoeff (g.ofConv h) := by
  rw [positiveLoopEvalZero, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    PowerSeries.constantCoeffAlgHom_apply]

/-- The values of a constant loop are the constant power series on the values of the point. -/
@[simp]
theorem ofConv_constantPositiveLoop_apply (g : WithConv (H →ₐ[k] R)) (h : H) :
    (constantPositiveLoop k H R g).ofConv h = PowerSeries.C (g.ofConv h) := by
  rw [constantPositiveLoop, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', PowerSeries.algebraMap_eq]

/-- The constant loops are a section of evaluation at `X = 0`. -/
@[simp]
theorem positiveLoopEvalZero_constantPositiveLoop (g : WithConv (H →ₐ[k] R)) :
    positiveLoopEvalZero k H R (constantPositiveLoop k H R g) = g := by
  rw [positiveLoopEvalZero, constantPositiveLoop, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp,
    PowerSeries.constantCoeffAlgHom_comp_toAlgHom, AlgHom.mapValue_id, MonoidHom.id_apply]

/-- The kernel of evaluation at `X = 0` is the congruence subgroup `K_1(R)` of level `(X)`. -/
theorem ker_positiveLoopEvalZero :
    (positiveLoopEvalZero k H R).ker = congruenceSubgroup k H (Ideal.span {PowerSeries.X}) := by
  rw [positiveLoopEvalZero, ker_mapValue_eq_congruenceSubgroup, ← PowerSeries.ker_constantCoeff]
  congr 1
  ext f
  rw [RingHom.mem_ker, RingHom.mem_ker, PowerSeries.constantCoeffAlgHom_apply]

end EvalZero

section Colimit

/-- **The coordinate Hopf algebra of the positive loop group.** The directed colimit of the jet
Hopf algebras `jetHopfAlgebra k H N` along the truncations `jetTruncation k H N`, the coordinate
ring of the inverse limit `L⁺G = lim_N J_N G` of the jet groups. Its points over `R` are
`L⁺G(R) = G(R⟦X⟧)` (`positiveLoopPointsMulEquiv`). -/
abbrev positiveLoopHopfAlgebra : Type _ :=
  DirectLimit (jetHopfAlgebra k H) (BialgHom.natLERec (jetTruncation k H))

variable (R : Type*) [CommRing R] [Algebra k R]

-- The compatible families of points of the jet groups form the inverse limit `jetLimit`.
private theorem pointsLimit_eq_jetLimit :
    DirectLimit.pointsLimit (BialgHom.natLERec (jetTruncation k H)) R =
      (jetLimit k H R).toSubmonoid := by
  ext x
  exact BialgHom.mem_pointsLimit_natLERec_iff _

/-- **The points of `positiveLoopHopfAlgebra k H` are the positive loops.** The group
isomorphism `Hom(positiveLoopHopfAlgebra k H, R) ≃* L⁺G(R) = G(R⟦X⟧)`: a point of the colimit is a
compatible sequence of points of the jet groups (`DirectLimit.pointsMulEquiv`), which is the
sequence of jets of a unique positive loop (`positiveLoopJetLimitMulEquiv`). It is natural in `R`
(`positiveLoopPointsMulEquiv_naturality`) and compatible with the projections to the jet groups
(`jetProjection_positiveLoopPointsMulEquiv`). -/
noncomputable def positiveLoopPointsMulEquiv :
    WithConv (positiveLoopHopfAlgebra k H →ₐ[k] R) ≃* WithConv (H →ₐ[k] R⟦X⟧) :=
  (DirectLimit.pointsMulEquiv _ R).trans <|
    (MulEquiv.submonoidCongr (pointsLimit_eq_jetLimit k H R)).trans
      (positiveLoopJetLimitMulEquiv k H R).symm

variable {k H R}

/-- **Compatibility with the projections to the jet groups.** The `N`-jet of the loop attached to
a point of `positiveLoopHopfAlgebra k H` is the restriction of the point to the `N`-th stage. -/
@[simp]
theorem jetProjection_positiveLoopPointsMulEquiv
    (x : WithConv (positiveLoopHopfAlgebra k H →ₐ[k] R)) (N : ℕ) :
    jetProjection k H R N (positiveLoopPointsMulEquiv k H R x) =
      BialgHom.mapDomain (DirectLimit.Bialgebra.of _ _ N) x := by
  rw [← positiveLoopJetLimitMulEquiv_apply, positiveLoopPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  exact DirectLimit.pointsMulEquiv_apply x N

/-- The restriction to the `N`-th stage of the point of `positiveLoopHopfAlgebra k H` attached to
a positive loop is the `N`-jet of the loop. -/
theorem mapDomain_of_positiveLoopPointsMulEquiv_symm (g : WithConv (H →ₐ[k] R⟦X⟧)) (N : ℕ) :
    BialgHom.mapDomain (DirectLimit.Bialgebra.of _ _ N)
        ((positiveLoopPointsMulEquiv k H R).symm g) =
      jetProjection k H R N g := by
  rw [← jetProjection_positiveLoopPointsMulEquiv, MulEquiv.apply_symm_apply]

/-- **Naturality of `positiveLoopPointsMulEquiv` in `R`.** For `φ : R →ₐ[k] S`, the loop attached
to the image of a point under `φ` is the coefficientwise image under `φ` of its loop. -/
theorem positiveLoopPointsMulEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (φ : R →ₐ[k] S) (x : WithConv (positiveLoopHopfAlgebra k H →ₐ[k] R)) :
    positiveLoopPointsMulEquiv k H S (AlgHom.mapValue φ x) =
      AlgHom.mapValue (PowerSeries.mapAlgHom φ) (positiveLoopPointsMulEquiv k H R x) := by
  refine (positiveLoopJetLimitMulEquiv k H S).injective (Subtype.ext (funext fun N ↦ ?_))
  rw [positiveLoopJetLimitMulEquiv_naturality, positiveLoopJetLimitMulEquiv_apply,
    positiveLoopJetLimitMulEquiv_apply, jetProjection_positiveLoopPointsMulEquiv,
    jetProjection_positiveLoopPointsMulEquiv, ← DirectLimit.pointsMulEquiv_apply,
    DirectLimit.pointsMulEquiv_mapValue, DirectLimit.pointsMulEquiv_apply]

end Colimit

section Trivial

variable (R : Type*) [CommRing R] [Algebra k R]

-- The positive loop group of the trivial group has a single point over every `R`.
private theorem subsingleton_positiveLoopHopfAlgebra_self_algHom :
    Subsingleton (positiveLoopHopfAlgebra k k →ₐ[k] R) :=
  ⟨fun _ _ ↦ WithConv.toConv_injective <| (positiveLoopPointsMulEquiv k k R).injective <|
    WithConv.ofConv_injective (Subsingleton.elim _ _)⟩

/-- **The positive loop group of the trivial group.** For the trivial group `G = Spec k`, the
coordinate Hopf algebra `positiveLoopHopfAlgebra k k` of `L⁺G` is `k`, through its counit. -/
noncomputable def positiveLoopHopfAlgebraSelfAlgEquiv : positiveLoopHopfAlgebra k k ≃ₐ[k] k :=
  have := subsingleton_positiveLoopHopfAlgebra_self_algHom k (positiveLoopHopfAlgebra k k)
  AlgEquiv.ofAlgHom (Bialgebra.counitAlgHom k _) (Algebra.ofId k _) (Subsingleton.elim _ _)
    (Subsingleton.elim _ _)

@[simp]
theorem positiveLoopHopfAlgebraSelfAlgEquiv_apply (x : positiveLoopHopfAlgebra k k) :
    positiveLoopHopfAlgebraSelfAlgEquiv k x = Coalgebra.counit x := (rfl)

end Trivial

end TauCeti.HopfAlgebra
