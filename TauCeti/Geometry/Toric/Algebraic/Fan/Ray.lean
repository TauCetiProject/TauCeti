/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

/-!
# Rays of a finite toric fan

A ray of a fan is a one-dimensional cone belonging to the fan. This intrinsic indexing type is
finite and agrees, below any cone of the fan, with the rays of that cone. Every nonzero cone of a
fan contains a ray; this follows from the generation of a toric cone by its rays.

The global ray type is the natural index for invariant boundary components of a toric variety.
Containment of cones is detected by their rays, and any set of rays lying in a simplicial cone
is the ray set of one of its faces. These facts determine which boundary components intersect.
Fan equivalences transport rays functorially, and the rays of an open subfan embed as exactly
the ambient rays whose cones belong to the subfan. These comparisons identify the indices of
boundary components under toric isomorphisms and restriction to invariant open subspaces.

## Main declarations

* `TauCeti.Toric.Fan.Ray`: the one-dimensional cones of a fan.
* `TauCeti.Toric.Fan.Ray.ofToricRay`: a ray of a cone of the fan, viewed as a fan ray.
* `TauCeti.Toric.Fan.Ray.toToricRay`: a fan ray contained in a cone, viewed as a ray of that cone.
* `TauCeti.Toric.Fan.rayEquiv`: the equivalence between rays below a cone and its toric rays.
* `TauCeti.Toric.Fan.exists_ray_le_of_ne_bot`: every nonzero cone of a fan contains a ray.
* `TauCeti.Toric.Fan.le_iff_forall_ray_le`: containment of cones is detected by their rays.
* `TauCeti.Toric.Fan.exists_cone_rays_eq`: a collection of rays in a simplicial cone is exactly
  the ray set of a face.
* `TauCeti.Toric.Fan.subfanRayEmbedding`: the ambient inclusion of the rays of an open subfan.
* `TauCeti.Toric.FanEquiv.rayEquiv`: the ray equivalence induced by a fan equivalence.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.2.
-/

public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i)

/-- A ray of a fan is a one-dimensional cone belonging to the fan. -/
abbrev Ray : Type _ :=
  {rho : Phi.cones //
    Module.finrank ℝ (Submodule.span ℝ (rho.1 : Set V)) = 1}

namespace Ray

/-- The cone of the fan underlying a fan ray. -/
abbrev toCone (rho : Phi.Ray) : Phi.cones := rho.1

/-- The cone underlying a fan ray has one-dimensional linear span. -/
@[simp]
theorem finrank_span (rho : Phi.Ray) :
    Module.finrank ℝ (Submodule.span ℝ (rho.toCone.1 : Set V)) = 1 :=
  rho.2

/-- A ray of a cone belonging to a fan is a ray of the fan. -/
def ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) : Phi.Ray :=
  ⟨⟨rho.toPointedCone, Phi.mem_of_isFaceOf sigma.2 rho.1.isFaceOf⟩, rho.2⟩

@[simp]
theorem toCone_ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone.1 = rho.toPointedCone :=
  (rfl)

/-- A toric ray, viewed as a fan ray, is contained in its original cone. -/
theorem toCone_ofToricRay_le (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone ≤ sigma := by
  exact Subtype.coe_le_coe.1 (toCone_ofToricRay Phi sigma rho ▸ rho.1.isFaceOf.le)

/-- A fan ray contained in a cone is a ray of that cone. -/
def toToricRay (rho : Phi.Ray) (sigma : Phi.cones) (h : rho.toCone ≤ sigma) :
    ToricRay sigma.1 :=
  ⟨⟨rho.toCone.1, Phi.isFaceOf_of_le sigma.2 rho.toCone.2 h⟩, rho.2⟩

@[simp]
theorem toPointedCone_toToricRay (rho : Phi.Ray) (sigma : Phi.cones)
    (h : rho.toCone ≤ sigma) :
    (rho.toToricRay Phi sigma h).toPointedCone = rho.toCone.1 :=
  (rfl)

/-- A fan ray is not the zero cone. -/
theorem toCone_ne_bot (rho : Phi.Ray) : rho.toCone.1 ≠ ⊥ := by
  exact (rho.toToricRay Phi rho.toCone le_rfl).toPointedCone_ne_bot

end Ray

/-- The fan rays contained in a cone are exactly the toric rays of that cone. -/
def rayEquiv (sigma : Phi.cones) :
    {rho : Phi.Ray // rho.toCone ≤ sigma} ≃ ToricRay sigma.1 where
  toFun rho := rho.1.toToricRay Phi sigma rho.2
  invFun rho := ⟨Ray.ofToricRay Phi sigma rho, rho.1.isFaceOf.le⟩
  left_inv rho := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv rho := by
    apply Subtype.ext
    apply PointedCone.Face.ext
    exact fun _ ↦ Iff.rfl

/-- The equivalence from fan rays below a cone to its toric rays uses the same underlying cone. -/
@[simp]
theorem rayEquiv_apply (sigma : Phi.cones)
    (rho : {rho : Phi.Ray // rho.toCone ≤ sigma}) :
    Phi.rayEquiv sigma rho = rho.1.toToricRay Phi sigma rho.2 :=
  (rfl)

/-- The inverse equivalence views a toric ray as a cone belonging to the fan. -/
@[simp]
theorem rayEquiv_symm_apply (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (Phi.rayEquiv sigma).symm rho =
      ⟨Ray.ofToricRay Phi sigma rho, Ray.toCone_ofToricRay_le Phi sigma rho⟩ :=
  (rfl)

/-- Every nonzero cone of a fan contains a ray of the fan. -/
theorem exists_ray_le_of_ne_bot (sigma : Phi.cones) (hσ : sigma.1 ≠ ⊥) :
    ∃ rho : Phi.Ray, rho.toCone ≤ sigma := by
  let rho := Classical.choice (ToricRay.nonempty_of_ne_bot
    (Phi.isToricCone sigma.2).fg (Phi.isToricCone sigma.2).salient hσ)
  exact ⟨Ray.ofToricRay Phi sigma rho, rho.1.isFaceOf.le⟩

/-- Containment of fan cones is detected by their rays. No regularity is needed. -/
theorem le_iff_forall_ray_le {sigma tau : Phi.cones} :
    sigma ≤ tau ↔ ∀ rho : Phi.Ray, rho.toCone ≤ sigma → rho.toCone ≤ tau := by
  refine ⟨fun h _ hrho ↦ hrho.trans h, fun h ↦ ?_⟩
  apply Subtype.coe_le_coe.mp
  rw [← ToricRay.iSup_toPointedCone (Phi.isToricCone sigma.2).fg
    (Phi.isToricCone sigma.2).salient]
  exact iSup_le fun rho ↦ h (Ray.ofToricRay Phi sigma rho)
    (Ray.toCone_ofToricRay_le Phi sigma rho)

/-- Any collection of rays contained in a simplicial cone of a fan is exactly the collection of
rays of a face of that cone. This includes the empty collection, which gives the zero cone. -/
theorem exists_cone_rays_eq {S : Set Phi.Ray} {sigma : Phi.cones}
    (hSigma : sigma.1.IsSimplicial) (hS : ∀ rho ∈ S, rho.toCone ≤ sigma) :
    ∃ tau : Phi.cones, tau ≤ sigma ∧ ∀ rho : Phi.Ray, rho.toCone ≤ tau ↔ rho ∈ S := by
  let A : Set (ToricRay sigma.1) := {rho | Ray.ofToricRay Phi sigma rho ∈ S}
  obtain ⟨F, hF⟩ := exists_face_rays_eq_of_isSimplicial hSigma A
  let tau : Phi.cones := ⟨F.toPointedCone, Phi.mem_of_isFaceOf sigma.2 F.isFaceOf⟩
  have hTau : tau ≤ sigma := F.isFaceOf.le
  have hRay (rho : Phi.Ray) (h : rho.toCone ≤ sigma) : rho.toCone ≤ tau ↔ rho ∈ S := by
    let nu := rho.toToricRay Phi sigma h
    have hInverse := congrArg Subtype.val ((Phi.rayEquiv sigma).symm_apply_apply ⟨rho, h⟩)
    simp only [rayEquiv_apply, rayEquiv_symm_apply, Subtype.coe_mk] at hInverse
    rw [← Subtype.coe_le_coe]
    simpa only [nu, Ray.toPointedCone_toToricRay, A, Set.mem_ofPred_eq,
      hInverse, tau] using hF nu
  refine ⟨tau, hTau, fun rho ↦ ⟨fun h ↦ (hRay rho (h.trans hTau)).mp h,
    fun h ↦ (hRay rho (hS rho h)).mpr h⟩⟩

section Subfan

variable (S : Set (PointedCone ℝ V)) (hS : S ⊆ Phi.cones)
  (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)

/-- The rays of an open subfan embed in the rays of the ambient fan without changing cones. -/
def subfanRayEmbedding : (Phi.subfan S hS hface).Ray ↪ Phi.Ray where
  toFun rho := ⟨⟨rho.toCone.1, hS (by simpa only [subfan_cones] using rho.toCone.2)⟩, rho.2⟩
  inj' := by
    intro rho tau h
    exact Subtype.ext (Subtype.ext (congrArg (fun r ↦ r.toCone.1) h))

/-- The ray embedding of a subfan leaves the underlying cone unchanged. -/
@[simp]
theorem toCone_subfanRayEmbedding (rho : (Phi.subfan S hS hface).Ray) :
    (Phi.subfanRayEmbedding S hS hface rho).toCone.1 = rho.toCone.1 :=
  (rfl)

/-- The rays coming from a subfan are exactly the ambient rays whose cones belong to it. -/
@[simp]
theorem range_subfanRayEmbedding :
    Set.range (Phi.subfanRayEmbedding S hS hface) = {rho | rho.toCone.1 ∈ S} := by
  ext rho
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨tau, rfl⟩
    simpa only [subfan_cones, toCone_subfanRayEmbedding] using tau.toCone.2
  · intro h
    exact ⟨⟨⟨rho.toCone.1, by simpa only [subfan_cones] using h⟩, rho.2⟩,
      Subtype.ext (Subtype.ext rfl)⟩

end Subfan

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' N'' V V' V'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V']
  [Module ℝ V''] {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {Phi : Fan i} {Psi : Fan i'} {Omega : Fan i''}

/-- A fan equivalence identifies the rays of the two fans by transporting their cones. -/
def rayEquiv (e : FanEquiv Phi Psi) : Phi.Ray ≃ Psi.Ray :=
  e.coneEquiv.toEquiv.subtypeEquiv fun sigma ↦ by
    simp only [OrderIso.coe_toEquiv, e.finrank_span_coneEquiv]

/-- The ray equivalence transports the underlying cone by the cone equivalence. -/
@[simp]
theorem toCone_rayEquiv (e : FanEquiv Phi Psi) (rho : Phi.Ray) :
    (e.rayEquiv rho).toCone = e.coneEquiv rho.toCone :=
  (rfl)

/-- The inverse ray equivalence is induced by the inverse fan equivalence. -/
@[simp]
theorem rayEquiv_symm (e : FanEquiv Phi Psi) : e.rayEquiv.symm = e.symm.rayEquiv := by
  simp only [rayEquiv, Equiv.subtypeEquiv_symm, ← coneEquiv_symm, OrderIso.toEquiv_symm]

/-- The identity fan equivalence induces the identity on rays. -/
@[simp]
theorem rayEquiv_refl (Phi : Fan i) : (FanEquiv.refl Phi).rayEquiv = Equiv.refl Phi.Ray := by
  apply Equiv.ext
  intro rho
  apply Subtype.ext
  simp only [toCone_rayEquiv, coneEquiv_refl, OrderIso.refl_apply, Equiv.refl_apply]

/-- Ray transport respects composition of fan equivalences. -/
@[simp]
theorem rayEquiv_trans (e : FanEquiv Phi Psi) (e' : FanEquiv Psi Omega) :
    (e.trans e').rayEquiv = e.rayEquiv.trans e'.rayEquiv := by
  simp only [rayEquiv, coneEquiv_trans]
  exact (Equiv.subtypeEquiv_trans _ _ _ _).symm

end TauCeti.Toric.FanEquiv
