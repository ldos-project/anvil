/* @Require heap_ok() && can_free(p) && valid_read(p, 4)
 * @Guarantee can_free(p) && valid_read(p, 4) && result >= 0
 * @Safety heap_ok()
 */
int external_measure(void);
