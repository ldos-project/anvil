/* @Require heap_ok() && can_free(p) && valid_read(p, 1)
 * @Guarantee can_free(p) && valid_read(p, 1) && result >= 0
 * @Safety heap_ok()
 */
int external_measure(void);
