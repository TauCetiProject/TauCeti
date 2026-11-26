/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.MappingSpace.Sphere.PathComponent

/-!
# Path components of unbased mapping spaces out of spheres

For `k ≥ 1`, the path components of the unbased mapping space `Map(S^k, X) = C(S^k, X)`, with the
compact-open topology, are the free homotopy classes of maps `S^k → X`. For a point `x` of `X`,
reading a generalized loop at `x` as a based map out of the sphere
(`TauCeti.basedMapSphereHomeomorph`) identifies the free homotopy classes of maps sending the
basepoint into the path component of `x` with the orbits of the action of `π₁(X, x)` on
`π_k(X, x)` (`TauCeti.homotopyGroupMulAction`). So for path-connected `X`

`π₀ Map(S^k, X) ≃ π_k(X, x) / π₁(X, x)`,

and when `X` is simply connected the action is trivial and the unbased mapping space has the same
path components as the based one, `π₀ Map(S^k, X) ≃ π_k(X, x) ≃ π₀ Map_*(S^k, X)`. For instance
`π₀ Map(Sⁿ, Sⁿ) ≃ ℤ` for `n ≥ 2`, in particular `π₀ Map(S², S²) ≃ ℤ`, by the degree.

The comparison rests on one fact
(`TauCeti.joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph`): two based maps
`f : (S^k, s₀) → (X, x)` and `g : (S^k, s₀) → (X, y)` are joined by a path in `Map(S^k, X)`
exactly when some homotopy of their generalized loops traces a path from `x` to `y` on the cube
boundary (`TauCeti.GenLoop.HomotopyAlong`). A path in `Map(S^k, X)` is a homotopy `I × S^k → X`,
read on the cube through the collapse `I^k → S^k`; conversely a homotopy along a path descends
through the collapse, which is a quotient map also after taking the product with `I`
(`TauCeti.isQuotientMap_prodMap_id_sphereCollapse`). The orbits of the action of `π₁(X, x)` are
exactly the classes joined by such homotopies along loops at `x`
(`TauCeti.homotopyGroup_mem_orbit_iff_exists_homotopyAlong`), and every map whose basepoint is
joined to `x` by a path `χ` is joined in `Map(S^k, X)` to the transport of its generalized loop
along `χ` (`TauCeti.GenLoop.collarHomotopyAlong`).

For `k = 1` the same comparison, with conjugacy classes of `π₁(X, x)` in place of the orbits, is
`TauCeti.conjClassesEquivFreeLoopComponents`.

## Main declarations

* `TauCeti.joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph`: based maps out of
  `S^k` are joined in the unbased mapping space exactly when their generalized loops are
  homotopic along a path.
* `TauCeti.sphereMapComponent`: the map `π_k(X, x) → π₀ Map(S^k, X)` forgetting the basepoint,
  with `TauCeti.sphereMapComponent_eq_iff`: two classes have the same image exactly when they lie
  in one orbit of `π₁(X, x)`.
* `TauCeti.sphereMapComponentOfOrbit`: the injective map `π_k(X, x) / π₁(X, x) → π₀ Map(S^k, X)`,
  whose range is the set of components of maps sending the basepoint into the path component of
  `x` (`TauCeti.range_sphereMapComponentOfOrbit`).
* `TauCeti.orbitEquivSphereMapComponents`: `π_k(X, x) / π₁(X, x) ≃ π₀ Map(S^k, X)` for
  path-connected `X`.
* `TauCeti.sphereMapComponentsEquivSigma`: `π₀ Map(S^k, X) ≃ Σ c, π_k(X, b_c) / π₁(X, b_c)` for
  any `X`, given a basepoint `b_c` in each path component `c`.
* `TauCeti.homotopyGroupEquivSphereMapComponents`: `π_k(X, x) ≃ π₀ Map(S^k, X)` for simply
  connected `X`, and `TauCeti.zerothHomotopyBasedMapEquivSphereMap`: forgetting the basepoint is
  then a bijection `π₀ Map_*(S^k, X) ≃ π₀ Map(S^k, X)`.
* `TauCeti.zerothHomotopySphereSelfMapEquivInt`: `π₀ Map(Sⁿ, Sⁿ) ≃ ℤ` for `n ≥ 2`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.A (basepoints and
  homotopy): for path-connected `X` the basepoint-free homotopy classes of maps `Sⁿ → X` are the
  orbits of the action of `π₁(X, x)` on `πₙ(X, x)`.
-/

public section

noncomputable section

open Metric Topology Topology.Homotopy
open scoped unitInterval

namespace TauCeti

variable (k : ℕ) [NeZero k] {X : Type*} [TopologicalSpace X]
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-! ### Paths of unbased maps are homotopies along paths -/

variable {k s₀} in
/-- **Based maps out of the sphere are joined in the unbased mapping space exactly when their
generalized loops are homotopic along a path.** For based maps `f : (S^k, s₀) → (X, x)` and
`g : (S^k, s₀) → (X, y)`, a path from `f` to `g` in `Map(S^k, X)` is a free homotopy, and its
value at the basepoint `s₀` is a path `γ` from `x` to `y`; read on the cube through the collapse
`I^k → S^k`, it is a homotopy between the generalized loops of `f` and `g` tracing `γ` on the cube
boundary. -/
theorem joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph {x y : X}
    {f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x}
    {g : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ y} :
    Joined f.val g.val ↔ ∃ γ : Path x y, Nonempty (GenLoop.HomotopyAlong γ
      (basedMapSphereHomeomorph k x s₀ f) (basedMapSphereHomeomorph k y s₀ g)) := by
  constructor
  · rintro ⟨P⟩
    refine ⟨(P.map (continuous_eval_const s₀)).cast f.property.symm g.property.symm, ⟨?_⟩⟩
    exact
      { toFun tz := P tz.1 (sphereCollapse k s₀ tz.2)
        continuous_toFun := by fun_prop
        map_zero_left z := by simp
        map_one_left z := by simp
        map_boundary t z hz :=
          congrArg (P t) ((sphereCollapse_eq_basepoint_iff k s₀ z).2 hz) }
  · rintro ⟨γ, ⟨h⟩⟩
    have hq := isQuotientMap_prodMap_id_sphereCollapse k s₀ I
    -- the homotopy along `γ` is constant on the fibres of the collapse, which meet the cube
    -- boundary only where the homotopy traces `γ`
    have hfac : Function.FactorsThrough h.toHomotopy.toContinuousMap
        ((ContinuousMap.id I).prodMap (sphereCollapse k s₀)) := by
      rintro ⟨t, z⟩ ⟨t', z'⟩ he
      obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
      rcases eq_or_mem_boundary_of_sphereCollapse_eq k s₀ he with rfl | ⟨hz, hz'⟩
      · rfl
      · exact (h.map_boundary t z hz).trans (h.map_boundary t z' hz').symm
    let H := hq.lift _ hfac
    have hH (t : I) (z : Fin k → I) : H (t, sphereCollapse k s₀ z) = h (t, z) :=
      DFunLike.congr_fun (hq.lift_comp _ hfac) (t, z)
    -- two maps out of the sphere agreeing after the collapse are equal
    have hext {φ ψ : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X)}
        (hφψ : ∀ z, φ (sphereCollapse k s₀ z) = ψ (sphereCollapse k s₀ z)) : φ = ψ :=
      (ContinuousMap.cancel_right (sphereCollapse_surjective k s₀)).1 (ContinuousMap.ext hφψ)
    -- the curried homotopy is a path from `f` to `g`
    exact ⟨⟨H.curry, hext fun z ↦ (hH 0 z).trans <| (h.apply_zero z).trans <|
        basedMapSphereHomeomorph_apply k x s₀ f z,
      hext fun z ↦ (hH 1 z).trans <| (h.apply_one z).trans <|
        basedMapSphereHomeomorph_apply k y s₀ g z⟩⟩

variable {k s₀} in
/-- A map out of the sphere whose basepoint is joined to `x` is joined in `Map(S^k, X)` to a map
sending the basepoint to `x`: the transport along the path of its generalized loop. -/
theorem exists_basedMap_joined_val {x : X}
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X)) (hf : Joined (f s₀) x) :
    ∃ g : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x, Joined f g.val := by
  let f' : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ (f s₀) := ⟨f, rfl⟩
  refine ⟨(basedMapSphereHomeomorph k x s₀).symm
    (GenLoop.transport hf.somePath (basedMapSphereHomeomorph k (f s₀) s₀ f')), ?_⟩
  refine (joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph (f := f')).2
    ⟨hf.somePath, ⟨?_⟩⟩
  rw [Homeomorph.apply_symm_apply]
  exact GenLoop.collarHomotopyAlong hf.somePath _

/-! ### Homotopy classes of based maps as unbased components -/

variable (x : X)

/-- The path component of the unbased mapping space `Map(S^k, X)` containing the based maps of a
homotopy class in `π_k(X, x)`: forgetting the basepoint on path components. Two classes have the
same image exactly when they lie in one orbit of `π₁(X, x)` (`TauCeti.sphereMapComponent_eq_iff`).
-/
def sphereMapComponent :
    HomotopyGroup (Fin k) X x →
      ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) :=
  Quotient.lift (fun p ↦ .mk ((basedMapSphereHomeomorph k x s₀).symm p).val) fun p q h ↦ by
    obtain ⟨K⟩ := h
    refine Quotient.sound (joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph.2
      ⟨Path.refl x, ?_⟩)
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    exact ⟨GenLoop.HomotopyAlong.ofHomotopyRel K⟩

/-- The class of a generalized loop `p` goes to the path component of the based map
`(basedMapSphereHomeomorph k x s₀).symm p`, read as an unbased map. -/
@[simp]
theorem sphereMapComponent_mk (p : Ω^ (Fin k) X x) :
    sphereMapComponent k s₀ x ⟦p⟧ = .mk ((basedMapSphereHomeomorph k x s₀).symm p).val :=
  (rfl)

/-- Through `π₀ Map_*(S^k, X) ≃ π_k(X, x)`, `sphereMapComponent` sends the path component of a
based map to the path component of the underlying unbased map. -/
theorem sphereMapComponent_zerothHomotopyBasedMapSphereEquiv_mk
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    sphereMapComponent k s₀ x (zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk f)) = .mk f.val := by
  rw [zerothHomotopyBasedMapSphereEquiv_mk, sphereMapComponent_mk, Homeomorph.symm_apply_apply]

variable {k s₀ x} in
/-- **Free homotopy classes of based maps are the orbits of `π₁(X, x)`.** Two classes of
`π_k(X, x)` give the same path component of `Map(S^k, X)` exactly when they lie in one orbit of the
action of the fundamental group. -/
theorem sphereMapComponent_eq_iff {a b : HomotopyGroup (Fin k) X x} :
    sphereMapComponent k s₀ x a = sphereMapComponent k s₀ x b ↔
      b ∈ MulAction.orbit (FundamentalGroup X x) a := by
  induction a using Quotient.inductionOn with | h p => ?_
  induction b using Quotient.inductionOn with | h q => ?_
  rw [sphereMapComponent_mk, sphereMapComponent_mk,
    homotopyGroup_mem_orbit_iff_exists_homotopyAlong rfl rfl]
  refine ZerothHomotopy.mk_eq_mk_iff.trans ?_
  rw [joined_val_iff_exists_homotopyAlong_basedMapSphereHomeomorph]
  simp

/-- The path component of `Map(S^k, X)` of the free homotopy class of based maps with a given
orbit of `π₁(X, x)` in `π_k(X, x)`. It is injective (`TauCeti.injective_sphereMapComponentOfOrbit`),
and for path-connected `X` a bijection (`TauCeti.orbitEquivSphereMapComponents`). -/
def sphereMapComponentOfOrbit :
    MulAction.orbitRel.Quotient (FundamentalGroup X x) (HomotopyGroup (Fin k) X x) →
      ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) :=
  Quotient.lift (sphereMapComponent k s₀ x) fun _ _ h ↦
    (sphereMapComponent_eq_iff.2 (MulAction.orbitRel_apply.1 h)).symm

/-- The orbit of a class `a` goes to the path component `sphereMapComponent k s₀ x a`. -/
@[simp]
theorem sphereMapComponentOfOrbit_mk (a : HomotopyGroup (Fin k) X x) :
    sphereMapComponentOfOrbit k s₀ x (Quotient.mk _ a) = sphereMapComponent k s₀ x a :=
  (rfl)

/-- Free homotopy classes determine orbits: distinct orbits of `π₁(X, x)` on `π_k(X, x)` give
distinct path components of `Map(S^k, X)`. -/
theorem injective_sphereMapComponentOfOrbit :
    Function.Injective (sphereMapComponentOfOrbit k s₀ x) := by
  intro a b h
  induction a using Quotient.inductionOn with | h a => ?_
  induction b using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound (MulAction.orbitRel_apply.2 (sphereMapComponent_eq_iff.1 h.symm))

variable (X) in
/-- The path component of the basepoints of the maps in a path component of `Map(S^k, X)`:
evaluation at the basepoint `s₀` on path components. -/
def sphereMapComponentBase :
    ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) → ZerothHomotopy X :=
  Quotient.map (fun f ↦ f s₀) fun _ _ h ↦ h.map (continuous_eval_const s₀)

omit [NeZero k] in
@[simp]
theorem sphereMapComponentBase_mk (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X)) :
    sphereMapComponentBase k X s₀ (.mk f) = .mk (f s₀) :=
  (rfl)

@[simp]
theorem sphereMapComponentBase_sphereMapComponent (a : HomotopyGroup (Fin k) X x) :
    sphereMapComponentBase k X s₀ (sphereMapComponent k s₀ x a) = .mk x := by
  induction a using Quotient.inductionOn with | h p => ?_
  rw [sphereMapComponent_mk, sphereMapComponentBase_mk]
  exact congrArg ZerothHomotopy.mk ((basedMapSphereHomeomorph k x s₀).symm p).property

/-- The free homotopy classes of based maps at `x` are the path components of `Map(S^k, X)` whose
maps send the basepoint into the path component of `x`. -/
theorem range_sphereMapComponentOfOrbit :
    Set.range (sphereMapComponentOfOrbit k s₀ x) =
      sphereMapComponentBase k X s₀ ⁻¹' {ZerothHomotopy.mk x} := by
  refine Set.Subset.antisymm ?_ fun c hc ↦ ?_
  · rintro _ ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | h a => ?_
    exact sphereMapComponentBase_sphereMapComponent k s₀ x a
  · obtain ⟨f, rfl⟩ := ZerothHomotopy.mk_surjective c
    rw [Set.mem_preimage, sphereMapComponentBase_mk, Set.mem_singleton_iff] at hc
    obtain ⟨g, hg⟩ := exists_basedMap_joined_val f (ZerothHomotopy.mk_eq_mk_iff.1 hc)
    refine ⟨Quotient.mk _ (zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk g)), ?_⟩
    rw [sphereMapComponentOfOrbit_mk, sphereMapComponent_zerothHomotopyBasedMapSphereEquiv_mk]
    exact (ZerothHomotopy.mk_eq_mk_iff.2 hg).symm

/-! ### Path-connected and simply connected targets -/

/-- **The path components of `Map(S^k, X)` for path-connected `X` are the orbits of `π₁(X, x)` on
`π_k(X, x)`:** `π_k(X, x) / π₁(X, x) ≃ π₀ Map(S^k, X)`, sending the orbit of the class of a based
map to the path component of the underlying unbased map. -/
def orbitEquivSphereMapComponents [PathConnectedSpace X] :
    MulAction.orbitRel.Quotient (FundamentalGroup X x) (HomotopyGroup (Fin k) X x) ≃
      ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) :=
  Equiv.ofBijective (sphereMapComponentOfOrbit k s₀ x)
    ⟨injective_sphereMapComponentOfOrbit k s₀ x, fun c ↦ by
      have hc : c ∈ Set.range (sphereMapComponentOfOrbit k s₀ x) := by
        rw [range_sphereMapComponentOfOrbit, Set.mem_preimage, Set.mem_singleton_iff]
        exact Subsingleton.elim _ _
      exact hc⟩

@[simp]
theorem orbitEquivSphereMapComponents_apply [PathConnectedSpace X]
    (a : MulAction.orbitRel.Quotient (FundamentalGroup X x) (HomotopyGroup (Fin k) X x)) :
    orbitEquivSphereMapComponents k s₀ x a = sphereMapComponentOfOrbit k s₀ x a :=
  (rfl)

/-- The inverse of `orbitEquivSphereMapComponents` sends the path component of the underlying
unbased map of a based map `f` to the orbit of the class of `f`. -/
@[simp]
theorem orbitEquivSphereMapComponents_symm_mk_val [PathConnectedSpace X]
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    (orbitEquivSphereMapComponents k s₀ x).symm (.mk f.val) =
      Quotient.mk _ (zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk f)) := by
  rw [Equiv.symm_apply_eq, orbitEquivSphereMapComponents_apply, sphereMapComponentOfOrbit_mk,
    sphereMapComponent_zerothHomotopyBasedMapSphereEquiv_mk]

/-- **The path components of `Map(S^k, X)` for any space `X`.** Given a basepoint `b_c` in each
path component `c` of `X`, the path components of `Map(S^k, X)` whose maps send the basepoint into
`c` are the orbits of `π₁(X, b_c)` on `π_k(X, b_c)`:
`π₀ Map(S^k, X) ≃ Σ c, π_k(X, b_c) / π₁(X, b_c)`. -/
def sphereMapComponentsEquivSigma (B : PathComponentBasepoints X) :
    ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) ≃
      Σ c : ZerothHomotopy X, MulAction.orbitRel.Quotient (FundamentalGroup X (B.point c))
        (HomotopyGroup (Fin k) X (B.point c)) :=
  (Equiv.sigmaFiberEquiv (sphereMapComponentBase k X s₀)).symm.trans
    (Equiv.sigmaCongrRight fun c ↦
      ((Equiv.ofInjective _ (injective_sphereMapComponentOfOrbit k s₀ (B.point c))).trans
        (Equiv.subtypeEquivRight fun d ↦ by
          rw [range_sphereMapComponentOfOrbit, Set.mem_preimage, Set.mem_singleton_iff,
            B.mk_point])).symm)

@[simp]
theorem sphereMapComponentsEquivSigma_symm_apply (B : PathComponentBasepoints X)
    (p : Σ c : ZerothHomotopy X, MulAction.orbitRel.Quotient (FundamentalGroup X (B.point c))
      (HomotopyGroup (Fin k) X (B.point c))) :
    (sphereMapComponentsEquivSigma k s₀ B).symm p =
      sphereMapComponentOfOrbit k s₀ (B.point p.1) p.2 :=
  (rfl)

@[simp]
theorem sphereMapComponentsEquivSigma_apply_fst (B : PathComponentBasepoints X)
    (c : ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X)) :
    (sphereMapComponentsEquivSigma k s₀ B c).1 = sphereMapComponentBase k X s₀ c :=
  (rfl)

/-- **For simply connected `X`, `π_k(X, x)` is the set of path components of `Map(S^k, X)`:** the
action of `π₁(X, x)` is trivial, so free and based homotopy classes of maps `S^k → X` agree. -/
def homotopyGroupEquivSphereMapComponents [SimplyConnectedSpace X] :
    HomotopyGroup (Fin k) X x ≃
      ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) :=
  Equiv.ofBijective (sphereMapComponent k s₀ x)
    ⟨fun a b h ↦ by
      obtain ⟨γ, hγ⟩ := sphereMapComponent_eq_iff.1 h
      rw [← hγ]
      exact (fundamentalGroup_smul_eq_self γ a).symm,
    fun c ↦ by
      obtain ⟨a, ha⟩ := (orbitEquivSphereMapComponents k s₀ x).surjective c
      induction a using Quotient.inductionOn with | h a => ?_
      exact ⟨a, ha⟩⟩

@[simp]
theorem homotopyGroupEquivSphereMapComponents_apply [SimplyConnectedSpace X]
    (a : HomotopyGroup (Fin k) X x) :
    homotopyGroupEquivSphereMapComponents k s₀ x a = sphereMapComponent k s₀ x a :=
  (rfl)

/-- The inverse of `homotopyGroupEquivSphereMapComponents` sends the path component of the
underlying unbased map of a based map `f` to the class of `f`. -/
@[simp]
theorem homotopyGroupEquivSphereMapComponents_symm_mk_val [SimplyConnectedSpace X]
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    (homotopyGroupEquivSphereMapComponents k s₀ x).symm (.mk f.val) =
      zerothHomotopyBasedMapSphereEquiv k x s₀ (.mk f) := by
  rw [Equiv.symm_apply_eq, homotopyGroupEquivSphereMapComponents_apply,
    sphereMapComponent_zerothHomotopyBasedMapSphereEquiv_mk]

/-- **For simply connected `X`, the unbased mapping space `Map(S^k, X)` has the same path
components as the based one:** forgetting the basepoint is a bijection
`π₀ Map_*(S^k, X) ≃ π₀ Map(S^k, X)`. -/
def zerothHomotopyBasedMapEquivSphereMap [SimplyConnectedSpace X] :
    ZerothHomotopy (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) ≃
      ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, X) :=
  (zerothHomotopyBasedMapSphereEquiv k x s₀).trans (homotopyGroupEquivSphereMapComponents k s₀ x)

/-- The bijection `zerothHomotopyBasedMapEquivSphereMap` sends the path component of a based map
to the path component of the underlying unbased map. -/
@[simp]
theorem zerothHomotopyBasedMapEquivSphereMap_mk [SimplyConnectedSpace X]
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    zerothHomotopyBasedMapEquivSphereMap k s₀ x (.mk f) = .mk f.val := by
  rw [zerothHomotopyBasedMapEquivSphereMap, Equiv.trans_apply,
    homotopyGroupEquivSphereMapComponents_apply,
    sphereMapComponent_zerothHomotopyBasedMapSphereEquiv_mk]

/-- The inverse of `zerothHomotopyBasedMapEquivSphereMap` sends the path component of the
underlying unbased map of a based map `f` to the path component of `f`. -/
@[simp]
theorem zerothHomotopyBasedMapEquivSphereMap_symm_mk_val [SimplyConnectedSpace X]
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    (zerothHomotopyBasedMapEquivSphereMap k s₀ x).symm (.mk f.val) = .mk f :=
  (Equiv.symm_apply_eq _).2 (zerothHomotopyBasedMapEquivSphereMap_mk k s₀ x f).symm

/-! ### Self-maps of spheres -/

section Sphere

variable (n : ℕ) (b : OrthonormalBasis (Fin (n + 3)) ℝ (EuclideanSpace ℝ (Fin (n + 3))))
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)

/-- **`π₀ Map(Sᵐ, Sᵐ) ≅ ℤ` for `m ≥ 2`.** The path components of the space of all self-maps of the
sphere `S^(n+2) ⊆ ℝ^(n+3)` are in bijection with `ℤ`, through the based self-maps
(`TauCeti.zerothHomotopyBasedMapSphereSelfEquivInt`), since the sphere is simply connected; the
orthonormal basis `b` fixes the sign. For `n = 0` this is `π₀ Map(S², S²) ≅ ℤ`. -/
def zerothHomotopySphereSelfMapEquivInt :
    ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) ≃ ℤ :=
  (zerothHomotopyBasedMapEquivSphereMap (n + 2) s₀ s₀).symm.trans
    (zerothHomotopyBasedMapSphereSelfEquivInt n b s₀)

/-- The integer of the path component of the underlying map of a based self-map `f` of the sphere
is the integer of the path component of `f` among based self-maps. -/
@[simp]
theorem zerothHomotopySphereSelfMapEquivInt_mk_val
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) s₀ s₀) :
    zerothHomotopySphereSelfMapEquivInt n b s₀ (.mk f.val) =
      zerothHomotopyBasedMapSphereSelfEquivInt n b s₀ (.mk f) := by
  rw [zerothHomotopySphereSelfMapEquivInt, Equiv.trans_apply,
    zerothHomotopyBasedMapEquivSphereMap_symm_mk_val]

end Sphere

end TauCeti
